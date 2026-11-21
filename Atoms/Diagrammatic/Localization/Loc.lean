import Atoms.Diagrammatic.Localization.WalkingEquivalenceLift
import Atoms.Diagrammatic.Marked.Generators
import Atoms.Homotopical.Marked.Extension

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Homotopical Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

private noncomputable def locSiteObj : MarkedSite atomMarking → DiagSet.{u}
  | ⟨U, false, _⟩ => ball U
  | ⟨U, true, hU⟩ => walkingEquivalence U (hU rfl)

private theorem degenerate_of_not_isIso {x y : MarkedSite atomMarking} (g : x ⟶ y)
    (hx : x.isMarked = true) (hg : ¬ IsIso g.1) : atomMarking.Degenerate g.1 :=
  (g.2 hx).resolve_left fun h => hg h.2

private noncomputable def locSiteMap :
    ∀ {x y : MarkedSite atomMarking}, (x ⟶ y) → (locSiteObj x ⟶ locSiteObj y)
  | ⟨_, false, _⟩, ⟨_, false, _⟩, g => uliftYoneda.{u}.map g.1
  | ⟨_, false, _⟩, ⟨V, true, hV⟩, g => uliftYoneda.{u}.map g.1 ≫ toWalkingEquivalence V (hV rfl)
  | ⟨_, true, hU⟩, ⟨_, false, _⟩, g =>
    degenerateLift (hU rfl) g.1 ((g.2 rfl).resolve_left fun h => Bool.false_ne_true h.1)
  | ⟨_, true, hU⟩, ⟨V, true, hV⟩, g =>
    letI := Classical.dec (IsIso g.1)
    if h : IsIso g.1 then walkingEquivalenceMap (hV rfl) (hU rfl) (asIso g.1)
    else degenerateLift (hU rfl) g.1 (degenerate_of_not_isIso g rfl h) ≫
      toWalkingEquivalence V (hV rfl)

private noncomputable def locSiteι : ∀ x : MarkedSite atomMarking, ball.{u} x.obj ⟶ locSiteObj x
  | ⟨_, false, _⟩ => 𝟙 _
  | ⟨U, true, hU⟩ => toWalkingEquivalence U (hU rfl)

private theorem locSiteMap_of_unmarked {U : Atom} (hU : false = true → atomMarking.markable U)
    {y : MarkedSite atomMarking} (f : (⟨U, false, hU⟩ : MarkedSite atomMarking) ⟶ y) :
    locSiteMap f = uliftYoneda.{u}.map f.1 ≫ locSiteι y := by
  obtain ⟨V, _ | _, hV⟩ := y
  · exact (Category.comp_id _).symm
  · rfl

private theorem locSiteMap_of_isIso {U V : Atom} (hU : true = true → atomMarking.markable U)
    (hV : true = true → atomMarking.markable V)
    (g : (⟨U, true, hU⟩ : MarkedSite atomMarking) ⟶ ⟨V, true, hV⟩) (h : IsIso g.1) :
    locSiteMap g = walkingEquivalenceMap.{u} (hV rfl) (hU rfl) (asIso g.1) :=
  dif_pos h

private theorem locSiteMap_of_degenerate {U : Atom} (hU : true = true → atomMarking.markable U)
    {y : MarkedSite atomMarking} (g : (⟨U, true, hU⟩ : MarkedSite atomMarking) ⟶ y)
    (h : atomMarking.Degenerate g.1) :
    locSiteMap g = degenerateLift.{u} (hU rfl) g.1 h ≫ locSiteι y := by
  obtain ⟨V, _ | _, hV⟩ := y
  · exact (Category.comp_id _).symm
  · exact dif_neg (not_isIso_of_degenerate h)

private theorem locSiteι_comp_locSiteMap {x y : MarkedSite atomMarking} (g : x ⟶ y) :
    locSiteι x ≫ locSiteMap g = uliftYoneda.{u}.map g.1 ≫ locSiteι y := by
  obtain ⟨U, _ | _, hU⟩ := x
  · exact (Category.id_comp _).trans (locSiteMap_of_unmarked hU g)
  · rcases g.2 rfl with ⟨hy, hg⟩ | hg
    · obtain ⟨V, _ | _, hV⟩ := y
      · exact absurd hy Bool.false_ne_true
      · exact ((congrArg (_ ≫ ·) (locSiteMap_of_isIso hU hV g hg)).trans
          (toWalkingEquivalence_walkingEquivalenceMap _ _ _))
    · exact (congrArg (_ ≫ ·) (locSiteMap_of_degenerate hU g hg)).trans
        (toWalkingEquivalence_degenerateLift_assoc _ _ _ _)

noncomputable def locSite : MarkedSite atomMarking ⥤ DiagSet.{u} where
  obj := locSiteObj
  map := locSiteMap
  map_id := by
    rintro ⟨U, _ | _, hU⟩
    · exact uliftYoneda.{u}.map_id U
    · exact (locSiteMap_of_isIso hU hU _ (inferInstanceAs (IsIso (𝟙 U)))).trans
        (walkingEquivalenceMap_refl _ _)
  map_comp := by
    rintro ⟨U, _ | _, hU⟩ y z f g
    · rw [locSiteMap_of_unmarked hU (f ≫ g), locSiteMap_of_unmarked hU f]
      exact (congrArg (· ≫ _) (uliftYoneda.{u}.map_comp f.1 g.1)).trans
        ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (locSiteι_comp_locSiteMap g).symm).trans (Category.assoc _ _ _).symm))
    · rcases f.2 rfl with ⟨hy, hf⟩ | hf
      · obtain ⟨V, _ | _, hV⟩ := y
        · exact absurd hy Bool.false_ne_true
        · rcases g.2 rfl with ⟨hz, hg⟩ | hg
          · obtain ⟨W, _ | _, hW⟩ := z
            · exact absurd hz Bool.false_ne_true
            · rw [locSiteMap_of_isIso hU hW (f ≫ g) (inferInstanceAs (IsIso (f.1 ≫ g.1))),
                locSiteMap_of_isIso hU hV f hf, locSiteMap_of_isIso hV hW g hg]
              exact walkingEquivalenceMap_comp _ _ _ _ _ _
          · rw [locSiteMap_of_degenerate hU (f ≫ g) (hg.iso_comp f.1),
              locSiteMap_of_isIso hU hV f hf, locSiteMap_of_degenerate hV g hg]
            exact (congrArg (· ≫ _) (walkingEquivalenceMap_degenerateLift _ _ (asIso f.1) g.1
              hg).symm).trans (Category.assoc _ _ _)
      · rw [locSiteMap_of_degenerate hU (f ≫ g) (hf.comp g.1), locSiteMap_of_degenerate hU f hf]
        exact (congrArg (· ≫ _) (degenerateLift_comp _ _ _ _)).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (locSiteι_comp_locSiteMap g).symm).trans
            (Category.assoc _ _ _).symm))

theorem locSite_obj_unmarked (U : Atom) :
    locSite.{u}.obj ((MarkedSite.unmarked atomMarking).obj U) = ball U :=
  rfl

theorem locSite_obj_marked (U : Atom) (hU : 0 < U.dimension) :
    locSite.{u}.obj (MarkedSite.marked U hU) = walkingEquivalence U hU :=
  rfl

theorem locSite_map_unmarked {U V : Atom} (g : U ⟶ V) :
    locSite.map ((MarkedSite.unmarked atomMarking).map g) =
      eqToHom (locSite_obj_unmarked U) ≫ uliftYoneda.{u}.map g ≫
        eqToHom (locSite_obj_unmarked V).symm := by
  change uliftYoneda.map g = 𝟙 _ ≫ uliftYoneda.map g ≫ 𝟙 _
  simp

theorem locSite_map_toSelf (U : Atom) (hU : 0 < U.dimension) :
    locSite.{u}.map (MarkedSite.toSelf (MarkedSite.marked (D := atomMarking) U hU)) =
      eqToHom (locSite_obj_unmarked U) ≫ toWalkingEquivalence U hU ≫
        eqToHom (locSite_obj_marked U hU).symm := by
  change uliftYoneda.{u}.map (𝟙 U) ≫ toWalkingEquivalence U hU =
    𝟙 _ ≫ toWalkingEquivalence U hU ≫ 𝟙 _
  simp

theorem toWalkingEquivalence_comp_locSite_map {U V : Atom} (hU : 0 < U.dimension)
    (g : MarkedSite.marked (D := atomMarking) U hU ⟶ (MarkedSite.unmarked atomMarking).obj V) :
    toWalkingEquivalence U hU ≫ eqToHom (locSite_obj_marked U hU).symm ≫ locSite.map g =
      uliftYoneda.{u}.map g.1 ≫ eqToHom (locSite_obj_unmarked V).symm := by
  change toWalkingEquivalence U hU ≫ 𝟙 _ ≫ degenerateLift hU g.1
    ((g.2 rfl).resolve_left fun h => Bool.false_ne_true h.1) =
    uliftYoneda.map g.1 ≫ 𝟙 _
  exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans
    ((toWalkingEquivalence_degenerateLift hU g.1
      ((g.2 rfl).resolve_left fun h => Bool.false_ne_true h.1)).trans (Category.comp_id _).symm)

noncomputable def Loc : MarkedDiagSet.{u} ⥤ DiagSet.{u} := MarkedPresheaf.extend locSite

noncomputable def reversibleArrow : DiagSet.{u} :=
  walkingEquivalence (atomGlobe 1) ((dimension_atomGlobe 1).symm ▸ Nat.one_pos)

private noncomputable def locAdjunction :
    uliftYoneda.{u}.leftKanExtension locSite.{u} ⊣ Presheaf.restrictedULiftYoneda.{u} locSite :=
  Presheaf.uliftYonedaAdjunction _ (uliftYoneda.{u}.leftKanExtensionUnit locSite.{u})

private noncomputable def toLocCell (X : MarkedDiagSet.{u}) (V : Atom)
    (x : X.underlying.obj (op V)) :
    ball V ⟶ Loc.obj X :=
  ((locAdjunction.unit.app X.obj).app (op ((MarkedSite.unmarked atomMarking).obj V)) x).down

private theorem toLocCell_map (X : MarkedDiagSet.{u}) {V W : Atom} (g : W ⟶ V)
    (x : X.underlying.obj (op V)) :
    toLocCell X W (X.underlying.map g.op x) = uliftYoneda.{u}.map g ≫ toLocCell X V x := by
  have h := congrArg ULift.down (NatTrans.naturality_apply (locAdjunction.unit.app X.obj)
    ((MarkedSite.unmarked atomMarking).map g).op x)
  exact h

noncomputable def toLoc (X : MarkedDiagSet.{u}) : X.underlying ⟶ Loc.obj X where
  app V := ↾fun x => uliftYonedaEquiv (toLocCell X V.unop x)
  naturality V W g := by
    ext x
    exact (congrArg uliftYonedaEquiv (toLocCell_map X g.unop x)).trans
      (uliftYonedaEquiv_naturality _ _).symm

private theorem toLocCell_comp {X : MarkedDiagSet.{u}} {Y : DiagSet.{u}} (g : Loc.obj X ⟶ Y)
    (V : Atom) (x : X.underlying.obj (op V)) :
    toLocCell X V x ≫ g = uliftYonedaEquiv.symm ((toLoc X ≫ g).app (op V) x) :=
  (uliftYonedaEquiv.symm_apply_apply _).symm

private theorem homEquiv_app_unmarked {X : MarkedDiagSet.{u}} {Y : DiagSet.{u}} (g : Loc.obj X ⟶ Y)
    (V : Atom) (x : X.underlying.obj (op V)) :
    ((locAdjunction.homEquiv X.obj Y g).app (op ((MarkedSite.unmarked atomMarking).obj V))
      x).down = toLocCell X V x ≫ g :=
  congrArg (fun φ : X.obj ⟶ (Presheaf.restrictedULiftYoneda.{u} locSite).obj Y =>
    (φ.app (op ((MarkedSite.unmarked atomMarking).obj V))
    x).down) (locAdjunction.homEquiv_unit X.obj Y g)

@[reassoc]
theorem toLoc_naturality {X X' : MarkedDiagSet.{u}} (f : X ⟶ X') :
    toLoc X ≫ Loc.map f = MarkedPresheaf.forget.map f ≫ toLoc X' := by
  ext V x
  exact congrArg uliftYonedaEquiv (congrArg (fun φ => (φ.app (op ((MarkedSite.unmarked
    atomMarking).obj V.unop)) x).down) (locAdjunction.unit_naturality f.hom))

private noncomputable def toLocMarkedCell (X : MarkedDiagSet.{u}) {U : Atom} (hU : 0 < U.dimension)
    (s : X.obj.obj (op (MarkedSite.marked U hU))) : walkingEquivalence U hU ⟶ Loc.obj X :=
  ((locAdjunction.unit.app X.obj).app (op (MarkedSite.marked U hU)) s).down

private theorem unit_app_map_down (X : MarkedDiagSet.{u}) {x y : MarkedSite atomMarking} (g : x ⟶ y)
    (s : X.obj.obj (op y)) :
    ((locAdjunction.unit.app X.obj).app (op x) (X.obj.map g.op s)).down =
      locSite.map g ≫ ((locAdjunction.unit.app X.obj).app (op y) s).down := by
  have h := congrArg ULift.down (NatTrans.naturality_apply (locAdjunction.unit.app X.obj) g.op s)
  exact h

private theorem toLocCell_eq (X : MarkedDiagSet.{u}) (V : Atom) (x : X.underlying.obj (op V)) :
    toLocCell X V x = uliftYonedaEquiv.symm x ≫ toLoc X := by
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

noncomputable def locCell (X : MarkedDiagSet.{u}) {U : Atom} (hU : 0 < U.dimension)
    {x : X.underlying.obj (op U)} (hx : x ∈ X.marked U) : walkingEquivalence U hU ⟶ Loc.obj X :=
  toLocMarkedCell X hU hx.choose_spec.choose

private theorem locCell_congr (X : MarkedDiagSet.{u}) {U : Atom} (hU : 0 < U.dimension)
    {x x' : X.underlying.obj (op U)} (h : x = x') (hx : x ∈ X.marked U) (hx' : x' ∈ X.marked U) :
    locCell X hU hx = locCell X hU hx' := by
  subst h
  rfl

private theorem locCell_eq (X : MarkedDiagSet.{u}) {U : Atom} (hU : 0 < U.dimension)
    (s : X.obj.obj (op (MarkedSite.marked U hU)))
    (hx : X.obj.map (MarkedSite.toSelf (MarkedSite.marked U hU)).op s ∈ X.marked U) :
    locCell X hU hx = toLocMarkedCell X hU s :=
  congrArg (toLocMarkedCell X hU) (X.injective_map_toSelf _ hx.choose_spec.choose_spec)

@[reassoc]
theorem toWalkingEquivalence_locCell (X : MarkedDiagSet.{u}) {U : Atom} (hU : 0 < U.dimension)
    {x : X.underlying.obj (op U)} (hx : x ∈ X.marked U) :
    toWalkingEquivalence U hU ≫ locCell X hU hx = uliftYonedaEquiv.symm x ≫ toLoc X := by
  have h := unit_app_map_down X (MarkedSite.toSelf (MarkedSite.marked U hU))
    hx.choose_spec.choose
  rw [hx.choose_spec.choose_spec] at h
  have h' : locSite.map (MarkedSite.toSelf (MarkedSite.marked (D := atomMarking) U hU)) =
      toWalkingEquivalence U hU :=
    (locSite_map_toSelf U _).trans ((Category.id_comp _).trans (Category.comp_id _))
  rw [h'] at h
  exact h.symm.trans (toLocCell_eq X U x)

theorem locCell_map_iso (X : MarkedDiagSet.{u}) {U V : Atom} (hU : 0 < U.dimension)
    (hV : 0 < V.dimension) (e : V ≅ U) {x : X.underlying.obj (op U)} (hx : x ∈ X.marked U)
    (hx' : X.underlying.map e.hom.op x ∈ X.marked V) :
    locCell X hV hx' = walkingEquivalenceMap hU hV e ≫ locCell X hU hx := by
  let g : MarkedSite.marked (D := atomMarking) V hV ⟶ MarkedSite.marked U hU :=
    ⟨e.hom, fun _ => Or.inl ⟨rfl, Iso.isIso_hom e⟩⟩
  have hs : X.obj.map (MarkedSite.toSelf (MarkedSite.marked V hV)).op
      (X.obj.map g.op hx.choose_spec.choose) = X.underlying.map e.hom.op x :=
    (MarkedPresheaf.map_toSelf_map X g _).trans
      (congrArg (X.underlying.map e.hom.op) hx.choose_spec.choose_spec)
  refine (locCell_congr X hV hs.symm hx' (hs ▸ hx')).trans
    ((locCell_eq X hV _ (hs ▸ hx')).trans ((unit_app_map_down X g _).trans ?_))
  exact congrArg (· ≫ locCell X hU hx) ((locSiteMap_of_isIso (fun _ => hV) (fun _ => hU) g
    (Iso.isIso_hom e)).trans (congrArg (walkingEquivalenceMap hU hV) (Atom.iso_eq _ e)))

theorem locCell_of_isDegenerate (X : MarkedDiagSet.{u}) {U : Atom} (hU : 0 < U.dimension)
    {x : X.underlying.obj (op U)} (hx : x ∈ X.marked U) (hd : IsDegenerate X.underlying x) :
    locCell X hU hx = degenerateCellLift hU x hd ≫ toLoc X := by
  obtain ⟨W, p, y, hp, hni, rfl⟩ := hd
  have hg : atomMarking.Degenerate p := .of_degeneracy ⟨hp, hni⟩
  let g : MarkedSite.marked (D := atomMarking) U hU ⟶ (MarkedSite.unmarked atomMarking).obj W :=
    ⟨p, fun _ => Or.inr hg⟩
  have hs : X.obj.map (MarkedSite.toSelf (MarkedSite.marked U hU)).op (X.obj.map g.op y) =
      X.underlying.map p.op y :=
    (MarkedPresheaf.map_toSelf_map X g y).trans
      (congrArg (X.underlying.map p.op) (MarkedPresheaf.map_toSelf_unmarked X W y))
  refine (locCell_congr X hU hs.symm hx (hs ▸ hx)).trans
    ((locCell_eq X hU (X.obj.map g.op y) (hs ▸ hx)).trans ?_)
  refine (unit_app_map_down X g y).trans ?_
  refine (congrArg (· ≫ _) (rfl : locSite.map g = degenerateLift hU p hg)).trans ?_
  refine (congrArg (_ ≫ ·) (toLocCell_eq X W y)).trans ((Category.assoc _ _ _).symm.trans ?_)
  exact congrArg (· ≫ toLoc X) (degenerateLift_comp_yonedaEquiv_symm hU p hg y _)

private theorem homEquiv_app_down {X : MarkedDiagSet.{u}} {Y : DiagSet.{u}} (g : Loc.obj X ⟶ Y)
    (x : MarkedSite atomMarking) (s : X.obj.obj (op x)) :
    ((locAdjunction.homEquiv X.obj Y g).app (op x) s).down =
      ((locAdjunction.unit.app X.obj).app (op x) s).down ≫ g :=
  congrArg (fun φ : X.obj ⟶ (Presheaf.restrictedULiftYoneda.{u} locSite).obj Y =>
    (φ.app (op x) s).down) (locAdjunction.homEquiv_unit X.obj Y g)

theorem loc_hom_ext {X : MarkedDiagSet.{u}} {Z : DiagSet.{u}} {h h' : Loc.obj X ⟶ Z}
    (h₀ : toLoc X ≫ h = toLoc X ≫ h')
    (h₁ : ∀ (U : Atom) (hU : 0 < U.dimension) (x : X.underlying.obj (op U))
      (hx : x ∈ X.marked U), ¬ IsDegenerate X.underlying x →
        locCell X hU hx ≫ h = locCell X hU hx ≫ h') :
    h = h' := by
  apply (locAdjunction.homEquiv X.obj Z).injective
  ext ⟨x⟩ s
  apply ULift.ext
  have key : ((locAdjunction.unit.app X.obj).app (op x) s).down ≫ h =
      ((locAdjunction.unit.app X.obj).app (op x) s).down ≫ h' := by
    obtain ⟨U, _ | _, hU⟩ := x
    · change toLocCell X U s ≫ h = toLocCell X U s ≫ h'
      exact (toLocCell_comp h U s).trans
        ((congrArg (fun k : X.underlying ⟶ Z => uliftYonedaEquiv.symm (k.app (op U) s)) h₀).trans
          (toLocCell_comp h' U s).symm)
    · have hx : X.obj.map (MarkedSite.toSelf (MarkedSite.marked U (hU rfl))).op s ∈ X.marked U :=
        ⟨hU rfl, s, rfl⟩
      change toLocMarkedCell X (hU rfl) s ≫ h = toLocMarkedCell X (hU rfl) s ≫ h'
      rw [← locCell_eq X (hU rfl) s hx]
      by_cases hd : IsDegenerate X.underlying
        (X.obj.map (MarkedSite.toSelf (MarkedSite.marked U (hU rfl))).op s)
      · rw [locCell_of_isDegenerate X (hU rfl) hx hd, Category.assoc, h₀, ← Category.assoc]
      · exact h₁ U (hU rfl) _ hx hd
  exact (homEquiv_app_down h x s).trans (key.trans (homEquiv_app_down h' x s).symm)

noncomputable def markedAtomIsoYoneda (U : Atom) (hU : 0 < U.dimension) :
    MarkedDiagSet.markedAtom.{u} U hU ≅
      (MarkedPresheaf.yoneda atomMarking).obj (MarkedSite.marked U hU) where
  hom := MarkedPresheaf.homMk
    { app V := ↾fun x => ULift.up (⟨x.down, fun h => absurd h Bool.false_ne_true⟩ :
        (MarkedSite.unmarked atomMarking).obj V.unop ⟶ MarkedSite.marked U hU)
      naturality V W φ := rfl } fun V x hx => by
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ V x).1 hx with ⟨W, p, y, hp, hni, hy⟩ | hx
    · exact ⟨dimension_pos_of_isDegenerate ⟨W, p, y, hp, hni, hy⟩,
        ⟨⟨x.down, fun _ => Or.inr ⟨W, p, y.down, ⟨hp, hni⟩, congrArg ULift.down hy⟩⟩⟩, rfl⟩
    · exact ⟨hU.trans_eq (Atom.dimension_eq_of_iso (asIso (x.down : V ⟶ U))).symm,
        ⟨⟨x.down, fun _ => Or.inl ⟨rfl, hx⟩⟩⟩, rfl⟩
  inv := MarkedPresheaf.homMk
    { app V := ↾fun g => ULift.up g.down.1
      naturality V W φ := rfl } fun V g ⟨h, ⟨y⟩, hy⟩ => by
    refine (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 ?_
    obtain rfl := hy
    rcases y.2 rfl with ⟨-, hiso⟩ | ⟨W, p, q, ⟨hp, hni⟩, hpq⟩
    · exact Or.inr hiso
    · exact Or.inl ⟨W, p, ⟨q⟩, hp, hni, congrArg ULift.up hpq⟩
  hom_inv_id := MarkedPresheaf.hom_ext rfl
  inv_hom_id := MarkedPresheaf.hom_ext rfl

noncomputable def locMarkedAtomIso (U : Atom) (hU : 0 < U.dimension) :
    Loc.{u}.obj (MarkedDiagSet.markedAtom U hU) ≅ walkingEquivalence U hU :=
  Loc.mapIso (markedAtomIsoYoneda U hU) ≪≫
    (MarkedPresheaf.yonedaCompExtendIso locSite.{u}).app (MarkedSite.marked U hU)

private def atomIsoSetoid : Setoid Atom where
  r U V := Nonempty (U ≅ V)
  iseqv := ⟨fun U => ⟨Iso.refl U⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩

private noncomputable def atomRep (U : Atom) : Atom := (Quotient.mk atomIsoSetoid U).out

private theorem nonempty_iso_atomRep (U : Atom) : Nonempty (U ≅ atomRep U) :=
  (atomIsoSetoid.symm (Quotient.mk_out (s := atomIsoSetoid) U))

private theorem atomRep_eq {U V : Atom} (h : Nonempty (U ≅ V)) : atomRep U = atomRep V :=
  congrArg Quotient.out (Quotient.sound (s := atomIsoSetoid) h)

section Rep

variable (Y : MarkedDiagSet.{u})

private def NondegRep : Type u :=
  {p : Σ R : Atom, diagram Y.underlying R //
    atomRep p.1 = p.1 ∧ p.2 ∈ Y.marked p.1 ∧ ¬ IsDegenerate Y.underlying p.2}

private theorem dimension_pos_nondegRep (n : NondegRep Y) : 0 < n.1.1.dimension :=
  Y.markable _ _ n.2.2.1

private noncomputable abbrev locTestAttach : (∐ fun n : NondegRep Y => ball n.1.1) ⟶ Y.underlying :=
  Sigma.desc fun n : NondegRep Y => uliftYonedaEquiv.symm n.1.2

private noncomputable abbrev locTestIncl : (∐ fun n : NondegRep Y => ball.{u} n.1.1) ⟶
    ∐ fun n : NondegRep Y => walkingEquivalence n.1.1 (dimension_pos_nondegRep Y n) :=
  Limits.Sigma.map fun n : NondegRep Y => toWalkingEquivalence n.1.1 (dimension_pos_nondegRep Y n)

private noncomputable abbrev locTest : DiagSet.{u} := pushout (locTestAttach Y) (locTestIncl Y)

private noncomputable abbrev locTestInl : Y.underlying ⟶ locTest Y :=
  pushout.inl (locTestAttach Y) (locTestIncl Y)

private theorem mono_locTestInl : Mono (locTestInl Y) := by
  have : ∀ n : NondegRep Y, Mono (toWalkingEquivalence n.1.1 (dimension_pos_nondegRep Y n)) :=
    fun n => inferInstanceAs (Mono (topInversionData _ _).toLocalization)
  exact (MorphismProperty.monomorphisms _).of_isPushout (IsPushout.of_hasPushout _ _)
    (inferInstanceAs (Mono (Limits.Sigma.map fun n : NondegRep Y =>
      toWalkingEquivalence n.1.1 (dimension_pos_nondegRep Y n))))

private noncomputable def locTestLeg (n : NondegRep Y) :
    walkingEquivalence n.1.1 (dimension_pos_nondegRep Y n) ⟶ locTest Y :=
  Sigma.ι (fun n : NondegRep Y => walkingEquivalence n.1.1 (dimension_pos_nondegRep Y n)) n ≫
    pushout.inr (locTestAttach Y) (locTestIncl Y)

private theorem toWalkingEquivalence_locTestLeg (n : NondegRep Y) :
    toWalkingEquivalence n.1.1 (dimension_pos_nondegRep Y n) ≫ locTestLeg Y n =
      uliftYonedaEquiv.symm n.1.2 ≫ locTestInl Y := by
  have h₁ := Limits.Sigma.ι_map
    (fun n : NondegRep Y => toWalkingEquivalence n.1.1 (dimension_pos_nondegRep Y n)) n
  have h₂ := Sigma.ι_desc (fun n : NondegRep Y => uliftYonedaEquiv.symm n.1.2) n
  have h₃ := pushout.condition (f := locTestAttach Y) (g := locTestIncl Y)
  rw [locTestLeg, ← Category.assoc, ← h₁, Category.assoc, ← h₃, ← Category.assoc, h₂]

private noncomputable def nondegRepOf {V : Atom} (c : Y.underlying.obj (op V))
    (hc : c ∈ Y.marked V) (hnd : ¬ IsDegenerate Y.underlying c) : NondegRep Y :=
  ⟨⟨atomRep V, Y.underlying.map (Classical.choice (nonempty_iso_atomRep V)).inv.op c⟩,
    atomRep_eq ⟨(Classical.choice (nonempty_iso_atomRep V)).symm⟩,
    (Y.transport (Classical.choice (nonempty_iso_atomRep V)).symm c).1 hc,
    fun h => hnd ((isDegenerate_map_iso_iff (Classical.choice (nonempty_iso_atomRep V)).symm c).1
      h)⟩

private theorem nondegRep_unique {V : Atom} {c : Y.underlying.obj (op V)} {n n' : NondegRep Y}
    (e : V ≅ n.1.1) (e' : V ≅ n'.1.1) (h : Y.underlying.map e.hom.op n.1.2 = c)
    (h' : Y.underlying.map e'.hom.op n'.1.2 = c) : n = n' := by
  revert e e' h h'
  obtain ⟨⟨R, s⟩, hR, -, -⟩ := n
  obtain ⟨⟨R', s'⟩, hR', -, -⟩ := n'
  intro e e' h h'
  obtain rfl : R = R' := hR.symm.trans ((atomRep_eq ⟨e.symm ≪≫ e'⟩).trans hR')
  have hee : e.inv ≫ e'.hom = 𝟙 R := congrArg Iso.hom (Atom.iso_eq (e.symm ≪≫ e') (Iso.refl R))
  have hs : s = s' := by
    simpa only [← Functor.map_comp_apply, ← op_comp, e.inv_hom_id, hee,
      op_id, Functor.map_id_apply] using
      congrArg (Y.underlying.map e.inv.op) (h.trans h'.symm)
  subst hs
  rfl

private theorem mem_marked_map_toSelf (x : MarkedSite atomMarking) (s : Y.obj.obj (op x)) :
    x.isMarked = true → Y.obj.map (MarkedSite.toSelf x).op s ∈ Y.marked x.obj := by
  obtain ⟨V, _ | _, hV⟩ := x
  · exact fun h => absurd h Bool.false_ne_true
  · exact fun _ => ⟨hV rfl, s, rfl⟩

variable {Z : DiagSet.{u}} (f : Y.underlying ⟶ Z)
  (leg : ∀ n : NondegRep Y, walkingEquivalence n.1.1 (dimension_pos_nondegRep Y n) ⟶ Z)

private noncomputable def descCell : ∀ (x : MarkedSite atomMarking)
    (c : Y.underlying.obj (op x.obj)), (x.isMarked = true → c ∈ Y.marked x.obj) →
      (locSite.obj x ⟶ Z)
  | ⟨_, false, _⟩, c, _ => uliftYonedaEquiv.symm c ≫ f
  | ⟨V, true, hV⟩, c, hc =>
    letI := Classical.dec (IsDegenerate Y.underlying c)
    if hd : IsDegenerate Y.underlying c then degenerateCellLift (hV rfl) c hd ≫ f
    else walkingEquivalenceMap (dimension_pos_nondegRep Y (nondegRepOf Y c (hc rfl) hd)) (hV rfl)
        (Classical.choice (nonempty_iso_atomRep V)) ≫ leg (nondegRepOf Y c (hc rfl) hd)

private theorem descCell_congr (x : MarkedSite atomMarking) {c c' : Y.underlying.obj (op x.obj)}
    (h : c = c') (hc : x.isMarked = true → c ∈ Y.marked x.obj)
    (hc' : x.isMarked = true → c' ∈ Y.marked x.obj) :
    descCell Y f leg x c hc = descCell Y f leg x c' hc' := by
  subst h
  rfl

private theorem descCell_degenerate {V : Atom} (hV : true = true → atomMarking.markable V)
    (c : Y.underlying.obj (op V)) (hc : true = true → c ∈ Y.marked V)
    (hd : IsDegenerate Y.underlying c) :
    descCell Y f leg ⟨V, true, hV⟩ c hc = degenerateCellLift (hV rfl) c hd ≫ f :=
  dif_pos hd

private theorem descCell_nondegenerate {V : Atom} (hV : true = true → atomMarking.markable V)
    (c : Y.underlying.obj (op V)) (hc : true = true → c ∈ Y.marked V)
    (hnd : ¬ IsDegenerate Y.underlying c) (n : NondegRep Y) (e : V ≅ n.1.1)
    (h : Y.underlying.map e.hom.op n.1.2 = c) :
    descCell Y f leg ⟨V, true, hV⟩ c hc =
      walkingEquivalenceMap (dimension_pos_nondegRep Y n) (hV rfl) e ≫ leg n := by
  refine (dif_neg hnd).trans ?_
  let e₀ := Classical.choice (nonempty_iso_atomRep V)
  have h₀ : Y.underlying.map e₀.hom.op (nondegRepOf Y c (hc rfl) hnd).1.2 = c := by
    simp [nondegRepOf, e₀, ← Functor.map_comp_apply, ← op_comp]
  obtain rfl := nondegRep_unique Y (n := nondegRepOf Y c (hc rfl) hnd) (n' := n) e₀ e h₀ h
  exact congrArg (fun e' => walkingEquivalenceMap _ (hV rfl) e' ≫ _) (Atom.iso_eq e₀ e)

private theorem toWalkingEquivalence_descCell
    (hleg : ∀ n : NondegRep Y, toWalkingEquivalence n.1.1 (dimension_pos_nondegRep Y n) ≫ leg n =
      uliftYonedaEquiv.symm n.1.2 ≫ f) {V : Atom}
    (hV : true = true → atomMarking.markable V) (c : Y.underlying.obj (op V))
    (hc : true = true → c ∈ Y.marked V) :
    toWalkingEquivalence V (hV rfl) ≫ descCell Y f leg ⟨V, true, hV⟩ c hc =
      uliftYonedaEquiv.symm c ≫ f := by
  by_cases hd : IsDegenerate Y.underlying c
  · exact (congrArg (_ ≫ ·) (dif_pos hd)).trans
      (toWalkingEquivalence_degenerateCellLift_assoc _ _ _ _)
  · let n := nondegRepOf Y c (hc rfl) hd
    let e₀ := Classical.choice (nonempty_iso_atomRep V)
    have h₀ : Y.underlying.map e₀.hom.op n.1.2 = c := by
      simp [n, nondegRepOf, e₀, ← Functor.map_comp_apply, ← op_comp]
    refine (congrArg (_ ≫ ·) (descCell_nondegenerate Y f leg hV c hc hd n e₀ h₀)).trans ?_
    refine ((toWalkingEquivalence_walkingEquivalenceMap_assoc _ _ e₀ _).trans ?_)
    refine (congrArg (uliftYoneda.{u}.map e₀.hom ≫ ·) (hleg n)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f)
      (((uliftYonedaEquiv_symm_map e₀.hom.op _).symm).trans
        (congrArg uliftYonedaEquiv.symm h₀)))

private theorem isDegenerate_map_of_degenerate {P : DiagSet.{u}} {U V : Atom} {g : U ⟶ V}
    (hg : atomMarking.Degenerate g) (c : P.obj (op V)) : IsDegenerate P (P.map g.op c) := by
  obtain ⟨W, p, q, ⟨hp, hni⟩, rfl⟩ := hg
  exact ⟨W, p, P.map q.op c, hp, hni, (Functor.map_comp_apply P q.op p.op c).symm⟩

private theorem descCell_map_cell
    (hleg : ∀ n : NondegRep Y, toWalkingEquivalence n.1.1 (dimension_pos_nondegRep Y n) ≫ leg n =
      uliftYonedaEquiv.symm n.1.2 ≫ f)
    {x y : MarkedSite atomMarking} (g : x ⟶ y)
    (c : Y.underlying.obj (op y.obj)) (hc : y.isMarked = true → c ∈ Y.marked y.obj)
    (hm : x.isMarked = true → Y.underlying.map g.1.op c ∈ Y.marked x.obj) :
    descCell Y f leg x _ hm = locSite.map g ≫ descCell Y f leg y c hc := by
  obtain ⟨U, _ | _, hU⟩ := x <;> obtain ⟨V, _ | _, hV⟩ := y
  · exact (congrArg (· ≫ f)
      (uliftYonedaEquiv_symm_map g.1.op c)).trans (Category.assoc _ _ _)
  · exact (congrArg (· ≫ f)
      (uliftYonedaEquiv_symm_map g.1.op c)).trans
      ((Category.assoc _ _ _).trans ((congrArg (uliftYoneda.{u}.map g.1 ≫ ·)
        (toWalkingEquivalence_descCell Y f leg hleg hV c hc).symm).trans
          (Category.assoc _ _ _).symm))
  · have hg : atomMarking.Degenerate g.1 :=
      (g.2 rfl).resolve_left fun h => Bool.false_ne_true h.1
    have hd := isDegenerate_map_of_degenerate hg c
    rw [descCell_degenerate Y f leg hU _ hm hd]
    exact (congrArg (· ≫ f)
      (degenerateLift_comp_yonedaEquiv_symm (hU rfl) g.1 hg c hd).symm).trans
      (Category.assoc _ _ _)
  · rcases g.2 rfl with ⟨-, hg⟩ | hg
    · by_cases hd : IsDegenerate Y.underlying c
      · have hd' : IsDegenerate Y.underlying (Y.underlying.map g.1.op c) :=
          (isDegenerate_map_iso_iff (asIso g.1) c).2 hd
        exact (dif_pos hd').trans ((congrArg (· ≫ f)
          (walkingEquivalenceMap_degenerateCellLift (hV rfl) (hU rfl) (asIso g.1) c hd
            hd').symm).trans
          ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
            (descCell_degenerate Y f leg hV c hc hd).symm).trans
            (congrArg (· ≫ _) (locSiteMap_of_isIso hU hV g hg).symm))))
      · have hd' : ¬ IsDegenerate Y.underlying (Y.underlying.map g.1.op c) :=
          fun h => hd ((isDegenerate_map_iso_iff (asIso g.1) c).1 h)
        let n := nondegRepOf Y c (hc rfl) hd
        let e₀ := Classical.choice (nonempty_iso_atomRep V)
        have h₀ : Y.underlying.map e₀.hom.op n.1.2 = c := by
          simp [n, nondegRepOf, e₀, ← Functor.map_comp_apply, ← op_comp]
        have h₁ : Y.underlying.map (asIso g.1 ≪≫ e₀).hom.op n.1.2 = Y.underlying.map g.1.op c :=
          (Functor.map_comp_apply Y.underlying e₀.hom.op g.1.op n.1.2).trans
            (congrArg (Y.underlying.map g.1.op) h₀)
        refine (descCell_nondegenerate Y f leg hU _ hm hd' n (asIso g.1 ≪≫ e₀) h₁).trans ?_
        refine ((congrArg (· ≫ leg n) (walkingEquivalenceMap_comp _ (hV rfl) (hU rfl)
          (asIso g.1) e₀ _)).trans (Category.assoc _ _ _)).trans ?_
        exact (congrArg (_ ≫ ·) (descCell_nondegenerate Y f leg hV c hc hd n e₀ h₀).symm).trans
          (congrArg (· ≫ _) (locSiteMap_of_isIso hU hV g hg).symm)
    · have hd := isDegenerate_map_of_degenerate hg c
      exact (dif_pos hd).trans ((congrArg (· ≫ f)
        (degenerateLift_comp_yonedaEquiv_symm (hU rfl) g.1 hg c hd).symm).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
          (toWalkingEquivalence_descCell Y f leg hleg hV c hc).symm).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ _) (locSiteMap_of_degenerate hU g hg).symm)))))

private noncomputable def descTranspose
    (hleg : ∀ n : NondegRep Y, toWalkingEquivalence n.1.1 (dimension_pos_nondegRep Y n) ≫ leg n =
      uliftYonedaEquiv.symm n.1.2 ≫ f) :
    Y.obj ⟶ (Presheaf.restrictedULiftYoneda.{u} locSite).obj Z where
  app x := ↾fun s => ULift.up (descCell Y f leg x.unop _ (mem_marked_map_toSelf Y x.unop s))
  naturality x y g := by
    ext s
    exact congrArg ULift.up ((descCell_congr Y f leg _ (MarkedPresheaf.map_toSelf_map _ g.unop s) _
      fun h => MarkedPresheaf.map_toSelf_map _ g.unop s ▸ mem_marked_map_toSelf Y _ _ h).trans
      (descCell_map_cell Y f leg hleg g.unop _ (mem_marked_map_toSelf Y x.unop s) _))

private theorem toLoc_comp_descTranspose
    (hleg : ∀ n : NondegRep Y, toWalkingEquivalence n.1.1 (dimension_pos_nondegRep Y n) ≫ leg n =
      uliftYonedaEquiv.symm n.1.2 ≫ f) :
    toLoc Y ≫ (locAdjunction.homEquiv _ _).symm (descTranspose Y f leg hleg) = f := by
  ext V x
  have h := (congrArg (fun ψ : Y.obj ⟶ (Presheaf.restrictedULiftYoneda.{u} locSite).obj
      Z => (ψ.app (op ((MarkedSite.unmarked atomMarking).obj V.unop)) x).down)
    (Equiv.apply_symm_apply (locAdjunction.homEquiv _ _) (descTranspose Y f leg hleg))).symm.trans
    (homEquiv_app_unmarked ((locAdjunction.homEquiv _ _).symm (descTranspose Y f leg hleg))
      V.unop x)
  exact (congrArg uliftYonedaEquiv h.symm).trans ((uliftYonedaEquiv_comp _ _).trans
    (congrArg ((f).app V) ((uliftYonedaEquiv.apply_symm_apply _).trans
      (MarkedPresheaf.map_toSelf_unmarked _ V.unop x))))

end Rep

theorem exists_toLoc_comp_eq (X : MarkedDiagSet.{u}) {Z : DiagSet.{u}} (f : X.underlying ⟶ Z)
    (leg : ∀ (U : Atom) (hU : 0 < U.dimension) (x : X.underlying.obj (op U)),
      x ∈ X.marked U → ¬ IsDegenerate X.underlying x → (walkingEquivalence U hU ⟶ Z))
    (hleg : ∀ U hU x hx hnd,
      toWalkingEquivalence U hU ≫ leg U hU x hx hnd = uliftYonedaEquiv.symm x ≫ f) :
    ∃ h : Loc.obj X ⟶ Z, toLoc X ≫ h = f ∧
      ∀ (U : Atom) (hU : 0 < U.dimension) (x : X.underlying.obj (op U))
        (hx : x ∈ X.marked U), ¬ IsDegenerate X.underlying x →
        ∃ (V : Atom) (hV : 0 < V.dimension) (y : X.underlying.obj (op V))
          (hy : y ∈ X.marked V) (hnd : ¬ IsDegenerate X.underlying y) (e : U ≅ V),
          X.underlying.map e.hom.op y = x ∧
            locCell X hU hx ≫ h = walkingEquivalenceMap hV hU e ≫ leg V hV y hy hnd := by
  let leg' : ∀ n : NondegRep X, walkingEquivalence n.1.1 (dimension_pos_nondegRep X n) ⟶ Z :=
    fun n => leg n.1.1 (dimension_pos_nondegRep X n) n.1.2 n.2.2.1 n.2.2.2
  have hleg' : ∀ n : NondegRep X, toWalkingEquivalence n.1.1 (dimension_pos_nondegRep X n) ≫
      leg' n = uliftYonedaEquiv.symm n.1.2 ≫ f := fun n => hleg _ _ _ _ _
  refine ⟨(locAdjunction.homEquiv _ _).symm (descTranspose X f leg' hleg'),
    toLoc_comp_descTranspose X f leg' hleg', ?_⟩
  intro U hU x hx hnd
  let n := nondegRepOf X x hx hnd
  let e₀ := Classical.choice (nonempty_iso_atomRep U)
  have h₀ : X.underlying.map e₀.hom.op n.1.2 = x := by
    simp [n, nondegRepOf, e₀, ← Functor.map_comp_apply, ← op_comp]
  refine ⟨n.1.1, dimension_pos_nondegRep X n, n.1.2, n.2.2.1, n.2.2.2, e₀, h₀, ?_⟩
  have hs := hx.choose_spec.choose_spec
  refine (homEquiv_app_down _ (MarkedSite.marked U hU) hx.choose_spec.choose).symm.trans ?_
  refine (congrArg (fun D : X.obj ⟶ (Presheaf.restrictedULiftYoneda.{u} locSite).obj Z =>
    (D.app (op (MarkedSite.marked U hU)) hx.choose_spec.choose).down)
      (Equiv.apply_symm_apply (locAdjunction.homEquiv _ _) (descTranspose X f leg' hleg'))).trans ?_
  exact descCell_nondegenerate X f leg' (fun _ => hU) _ (fun _ => hs.symm ▸ hx)
    (fun h => hnd (hs ▸ h)) n e₀
    (h₀.trans hs.symm)

instance mono_toLoc (Y : MarkedDiagSet.{u}) : Mono (toLoc Y) := by
  have := mono_locTestInl Y
  rw [← toLoc_comp_descTranspose Y _ _ (toWalkingEquivalence_locTestLeg Y)] at this
  exact mono_of_mono _ ((locAdjunction.homEquiv _ _).symm
    (descTranspose Y _ _ (toWalkingEquivalence_locTestLeg Y)))

section Flat

variable (P : DiagSet.{u})

private theorem hom_ext_flat {Y : DiagSet.{u}}
    {g g' : Loc.obj ((MarkedPresheaf.flat atomMarking).obj P) ⟶ Y}
    (h : toLoc _ ≫ g = toLoc _ ≫ g') : g = g' :=
  loc_hom_ext h fun U _ x hx hnd =>
    (hnd ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate P U x).1 hx)).elim

instance isIso_toLoc_flat : IsIso (toLoc ((MarkedPresheaf.flat atomMarking).obj P)) := by
  obtain ⟨g, hg, -⟩ := exists_toLoc_comp_eq ((MarkedPresheaf.flat atomMarking).obj P) (𝟙 P)
    (fun U _ x hx hnd => (hnd
      ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate P U x).1 hx)).elim)
    (fun U _ x hx hnd => (hnd
      ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate P U x).1 hx)).elim)
  exact ⟨⟨g, hg, hom_ext_flat P ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ toLoc _) hg).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm)))⟩⟩

end Flat

noncomputable def flatCompLocIso : MarkedPresheaf.flat atomMarking ⋙ Loc ≅ 𝟭 DiagSet.{u} :=
  (NatIso.ofComponents (fun P => @asIso _ _ _ _ (toLoc ((MarkedPresheaf.flat atomMarking).obj P))
      (isIso_toLoc_flat P))
    fun f => (toLoc_naturality ((MarkedPresheaf.flat atomMarking).map f)).symm).symm

private theorem isPushout_of_injective {A B C D : Type u} {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D}
    {b : C ⟶ D} (hw : t ≫ r = l ≫ b) (ht : Function.Injective t) (hr : Function.Injective r)
    (hb : Function.Injective b) (hinter : ∀ x y, r x = b y → ∃ a, l a = y)
    (hunion : ∀ d, (∃ x, r x = d) ∨ ∃ y, b y = d) : IsPushout t l r b := by
  have : Mono r := (mono_iff_injective r).2 hr
  refine Types.isPushout_of_isPullback_of_mono' ((Types.isPullback_iff t r l b).2
    ⟨hw, fun _ _ h => ht h.1, fun x₂ x₃ h => ?_⟩) ?_ fun _ _ _ _ h => hb h
  · obtain ⟨a, ha⟩ := hinter x₂ x₃ h
    refine ⟨a, hr ?_, ha⟩
    rw [h, ← ha]
    exact ConcreteCategory.congr_hom hw a
  · refine Set.eq_univ_of_forall fun d => ?_
    exact hunion d

private theorem isPushout_loc_map {A B C D : MarkedDiagSet.{u}} {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D}
    {b : C ⟶ D} (h : IsPushout ((ObjectProperty.ι _).map t) ((ObjectProperty.ι _).map l)
      ((ObjectProperty.ι _).map r) ((ObjectProperty.ι _).map b)) :
    IsPushout (Loc.map t) (Loc.map l) (Loc.map r) (Loc.map b) := by
  have w : t ≫ r = l ≫ b := ObjectProperty.hom_ext _ h.w
  obtain ⟨hL⟩ := MarkedPresheaf.isColimit_extend_mapCocone locSite
    ((PushoutCocone.isColimitMapCoconeEquiv (PushoutCocone.mk r b w) _).symm h.isColimit)
  exact IsPushout.of_isColimit ((PushoutCocone.isColimitMapCoconeEquiv _ Loc) hL)

private theorem exists_map_toSelf_eq (Y : MarkedDiagSet.{u}) (x : MarkedSite atomMarking)
    (c : Y.underlying.obj (op x.obj)) (hc : x.isMarked = true → c ∈ Y.marked x.obj) :
    ∃ s, Y.obj.map (MarkedSite.toSelf x).op s = c := by
  obtain ⟨V, _ | _, hV⟩ := x
  · exact ⟨c, Y.map_toSelf_unmarked V c⟩
  · obtain ⟨h', s, hs⟩ := hc rfl
    exact ⟨s, hs⟩

private theorem injective_app_of_injective {Y Y' : MarkedDiagSet.{u}} (φ : Y ⟶ Y')
    (x : MarkedSite atomMarking)
    (h : Function.Injective ((MarkedPresheaf.forget.map φ).app (op x.obj))) :
    Function.Injective (φ.hom.app (op x)) := fun s s' hs =>
  Y.injective_map_toSelf x (h ((MarkedPresheaf.forget_map_app_map_toSelf φ x s).trans
    ((congrArg _ hs).trans (MarkedPresheaf.forget_map_app_map_toSelf φ x s').symm)))

private theorem isPushout_ι_map {A B C D : MarkedDiagSet.{u}} {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D}
    {b : C ⟶ D} (hw : t ≫ r = l ≫ b)
    (ht : ∀ V, Function.Injective ((MarkedPresheaf.forget.map t).app (op V)))
    (hr : ∀ V, Function.Injective ((MarkedPresheaf.forget.map r).app (op V)))
    (hb : ∀ V, Function.Injective ((MarkedPresheaf.forget.map b).app (op V)))
    (hinter : ∀ (x : MarkedSite atomMarking) (cb : B.underlying.obj (op x.obj))
      (cc : C.underlying.obj (op x.obj)), (x.isMarked = true → cb ∈ B.marked x.obj) →
      (x.isMarked = true → cc ∈ C.marked x.obj) →
      (MarkedPresheaf.forget.map r).app _ cb = (MarkedPresheaf.forget.map b).app _ cc →
      ∃ ca, (x.isMarked = true → ca ∈ A.marked x.obj) ∧
        (MarkedPresheaf.forget.map l).app _ ca = cc)
    (hunion : ∀ (x : MarkedSite atomMarking) (cd : D.underlying.obj (op x.obj)),
      (x.isMarked = true → cd ∈ D.marked x.obj) →
      (∃ cb, (x.isMarked = true → cb ∈ B.marked x.obj) ∧
        (MarkedPresheaf.forget.map r).app _ cb = cd) ∨
      ∃ cc, (x.isMarked = true → cc ∈ C.marked x.obj) ∧
        (MarkedPresheaf.forget.map b).app _ cc = cd) :
    IsPushout ((ObjectProperty.ι _).map t) ((ObjectProperty.ι _).map l)
      ((ObjectProperty.ι _).map r) ((ObjectProperty.ι _).map b) := by
  refine IsPushout.of_forall_isPushout_app fun x => isPushout_of_injective
    (NatTrans.congr_app (congrArg (fun φ => φ.hom) hw) x)
    (injective_app_of_injective t x.unop (ht _)) (injective_app_of_injective r x.unop (hr _))
    (injective_app_of_injective b x.unop (hb _)) (fun m w h => ?_) (fun d => ?_)
  · obtain ⟨ca, hca, hl⟩ := hinter x.unop _ _ (mem_marked_map_toSelf B x.unop m)
      (mem_marked_map_toSelf C x.unop w)
      ((MarkedPresheaf.forget_map_app_map_toSelf r x.unop m).trans ((congrArg _ h).trans
        (MarkedPresheaf.forget_map_app_map_toSelf b x.unop w).symm))
    obtain ⟨z, hz⟩ := exists_map_toSelf_eq A x.unop ca hca
    exact ⟨z, C.injective_map_toSelf x.unop ((MarkedPresheaf.forget_map_app_map_toSelf l x.unop
      z).symm.trans ((congrArg _ hz).trans hl))⟩
  · rcases hunion x.unop _ (mem_marked_map_toSelf D x.unop d) with ⟨cb, hcb, hrb⟩ | ⟨cc, hcc, hbc⟩
    · obtain ⟨m, hm⟩ := exists_map_toSelf_eq B x.unop cb hcb
      exact Or.inl ⟨m, D.injective_map_toSelf x.unop ((MarkedPresheaf.forget_map_app_map_toSelf r
        x.unop m).symm.trans ((congrArg _ hm).trans hrb))⟩
    · obtain ⟨w, hw'⟩ := exists_map_toSelf_eq C x.unop cc hcc
      exact Or.inr ⟨w, D.injective_map_toSelf x.unop ((MarkedPresheaf.forget_map_app_map_toSelf b
        x.unop w).symm.trans ((congrArg _ hw').trans hbc))⟩

section Mono

variable {X X' : MarkedDiagSet.{u}} (f : X ⟶ X')

private def imageMarking : MarkedPresheaf.Marking atomMarking X'.underlying where
  marked V := {y | (∃ x ∈ X.marked V, (MarkedPresheaf.forget.map f).app (op V) x = y) ∨
    IsDegenerate X'.underlying y}
  markable V y h := h.elim (fun ⟨x, hx, _⟩ => X.markable V x hx) dimension_pos_of_isDegenerate
  degenerate _ b p hp y := Or.inr ⟨b, p, y, hp.1, hp.2, rfl⟩
  transport U V e y := by
    constructor
    · rintro (⟨x, hx, rfl⟩ | hd)
      · exact Or.inl ⟨X.underlying.map e.hom.op x, (X.transport e x).1 hx,
          NatTrans.naturality_apply (MarkedPresheaf.forget.map f) e.hom.op x⟩
      · exact Or.inr ((isDegenerate_map_iso_iff e y).2 hd)
    · rintro (⟨x, hx, hxy⟩ | hd)
      · refine Or.inl ⟨X.underlying.map e.inv.op x, (X.transport e.symm x).1 hx, ?_⟩
        refine (NatTrans.naturality_apply (MarkedPresheaf.forget.map f) e.inv.op x).trans ?_
        rw [hxy]
        exact Functor.map_hom_inv'_apply X'.underlying e.op y
      · exact Or.inr ((isDegenerate_map_iso_iff e y).1 hd)

private def newMarking : MarkedPresheaf.Marking atomMarking X'.underlying where
  marked V := {y | IsDegenerate X'.underlying y ∨
    (y ∈ X'.marked V ∧ y ∉ (imageMarking f).marked V)}
  markable V y h := h.elim dimension_pos_of_isDegenerate fun h => X'.markable V y h.1
  degenerate _ b p hp y := Or.inl ⟨b, p, y, hp.1, hp.2, rfl⟩
  transport _ _ e y := or_congr (isDegenerate_map_iso_iff e y).symm
    (and_congr (X'.transport e y) (not_congr ((imageMarking f).transport e y)))

private theorem marked_of_mem_imageMarking {V : Atom} {y : X'.underlying.obj (op V)}
    (hy : y ∈ (imageMarking f).marked V) : y ∈ X'.marked V :=
  hy.elim (fun ⟨_, hx, hxy⟩ => hxy ▸ MarkedPresheaf.map_mem_marked f hx)
    (MarkedDiagSet.mem_marked_of_isDegenerate X')

private theorem mono_loc_map_toMarking :
    Mono (Loc.map (MarkedPresheaf.homMk (X := MarkedPresheaf.ofMarking _ (imageMarking f))
      (Y := X') (𝟙 _) fun V _ hy => marked_of_mem_imageMarking f
        ((MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy))) := by
  let tB : (MarkedPresheaf.flat atomMarking).obj X'.underlying ⟶
      MarkedPresheaf.ofMarking _ (imageMarking f) :=
    MarkedPresheaf.homMk (𝟙 _) fun V y hy => (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (Or.inr ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V y).1 hy))
  let lB : (MarkedPresheaf.flat atomMarking).obj X'.underlying ⟶
      MarkedPresheaf.ofMarking _ (newMarking f) :=
    MarkedPresheaf.homMk (𝟙 _) fun V y hy => (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (Or.inl ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V y).1 hy))
  let bB : MarkedPresheaf.ofMarking _ (newMarking f) ⟶ X' :=
    MarkedPresheaf.homMk (𝟙 _) fun V y hy =>
      ((MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy).elim
        (MarkedDiagSet.mem_marked_of_isDegenerate X') And.left
  have h := isPushout_loc_map (isPushout_ι_map (t := tB) (l := lB) (b := bB)
    (r := MarkedPresheaf.homMk (X := MarkedPresheaf.ofMarking _ (imageMarking f))
      (Y := X') (𝟙 _) fun V _ hy => marked_of_mem_imageMarking f
        ((MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy))
    (MarkedPresheaf.hom_ext rfl) (fun _ => Function.injective_id) (fun _ => Function.injective_id)
    (fun _ => Function.injective_id) (fun x cb cc hcb hcc hrb => by
      have hrb' : cb = cc := hrb
      refine ⟨cc, fun hx => (MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ _ cc).2 ?_, rfl⟩
      rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 (hcc hx) with hd | ⟨_, hn⟩
      · exact hd
      · exact absurd (hrb' ▸ (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 (hcb hx)) hn)
    (fun x cd hcd => by
      by_cases hx : x.isMarked = true
      · by_cases hi : cd ∈ (imageMarking f).marked x.obj
        · exact Or.inl ⟨cd, fun _ => (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 hi, rfl⟩
        · exact Or.inr ⟨cd, fun _ => (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
            (Or.inr ⟨hcd hx, hi⟩), rfl⟩
      · exact Or.inl ⟨cd, fun h => absurd h hx, rfl⟩))
  have hl : Mono (Loc.map lB) := by
    have e := toLoc_naturality lB
    have h₀ : Mono (MarkedPresheaf.forget.map lB) := (inferInstance : Mono (𝟙 _))
    have h₁ : (MorphismProperty.monomorphisms _)
        (toLoc ((MarkedPresheaf.flat atomMarking).obj X'.underlying) ≫ Loc.map lB) := by
      rw [e]
      exact @mono_comp _ _ _ _ _ _ h₀ _ (mono_toLoc _)
    exact ((MorphismProperty.monomorphisms _).cancel_left_of_respectsIso _ _).1 h₁
  exact (MorphismProperty.monomorphisms _).of_isPushout h hl

variable [Mono f]

private theorem injective_forget_map (V : Atom) :
    Function.Injective ((MarkedPresheaf.forget.map f).app (op V)) :=
  (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 ((MarkedPresheaf.mono_iff f).1
    inferInstance) (op V))

private theorem mono_loc_map_imageMarking :
    Mono (Loc.map (MarkedPresheaf.homMk (Y := MarkedPresheaf.ofMarking _ (imageMarking f))
      (MarkedPresheaf.forget.map f) fun V x hx =>
        (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 (Or.inl ⟨x, hx, rfl⟩))) := by
  have : Mono (MarkedPresheaf.forget.map f) := (MarkedPresheaf.mono_iff f).1 inferInstance
  let cA : (MarkedPresheaf.flat atomMarking).obj X.underlying ⟶ X :=
    MarkedPresheaf.homMk (𝟙 _) fun V x hx => MarkedDiagSet.mem_marked_of_isDegenerate X
      ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V x).1 hx)
  let rA : X ⟶ MarkedPresheaf.ofMarking _ (imageMarking f) :=
    MarkedPresheaf.homMk (MarkedPresheaf.forget.map f) fun V x hx =>
      (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 (Or.inl ⟨x, hx, rfl⟩)
  let bA : (MarkedPresheaf.flat atomMarking).obj X'.underlying ⟶
      MarkedPresheaf.ofMarking _ (imageMarking f) :=
    MarkedPresheaf.homMk (𝟙 _) fun V y hy => (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (Or.inr ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V y).1 hy))
  have h := isPushout_loc_map (isPushout_ι_map (t := cA)
    (l := (MarkedPresheaf.flat atomMarking).map (MarkedPresheaf.forget.map f)) (r := rA) (b := bA)
    (MarkedPresheaf.hom_ext rfl) (fun _ => Function.injective_id) (injective_forget_map f)
    (fun _ => Function.injective_id) (fun x cb cc _ hcc hrb => by
      have hrb' : (MarkedPresheaf.forget.map f).app (op x.obj) cb = cc := hrb
      refine ⟨cb, fun hx => (MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ _ cb).2
        (isDegenerate_of_isDegenerate_app (MarkedPresheaf.forget.map f) ?_), hrb'⟩
      rw [hrb']
      exact (MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ _ cc).1 (hcc hx))
    (fun x cd hcd => by
      by_cases hx : x.isMarked = true
      · rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 (hcd hx) with
          ⟨c, hc, hcd'⟩ | hd
        · exact Or.inl ⟨c, fun _ => hc, hcd'⟩
        · exact Or.inr ⟨cd, fun _ => (MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ _ cd).2 hd,
            rfl⟩
      · exact Or.inr ⟨cd, fun h => absurd h hx, rfl⟩))
  have hl : Mono (Loc.map ((MarkedPresheaf.flat atomMarking).map
      (MarkedPresheaf.forget.map f))) := by
    have e := toLoc_naturality ((MarkedPresheaf.flat atomMarking).map (MarkedPresheaf.forget.map f))
    have h₀ : Mono (MarkedPresheaf.forget.map ((MarkedPresheaf.flat atomMarking).map
      (MarkedPresheaf.forget.map f))) := this
    have h₁ : (MorphismProperty.monomorphisms _) (toLoc ((MarkedPresheaf.flat atomMarking).obj
        (MarkedPresheaf.forget.obj X)) ≫ Loc.map ((MarkedPresheaf.flat atomMarking).map
          (MarkedPresheaf.forget.map f))) := by
      rw [e]
      exact @mono_comp _ _ _ _ _ _ h₀ _ (mono_toLoc _)
    exact ((MorphismProperty.monomorphisms _).cancel_left_of_respectsIso _ _).1 h₁
  exact (MorphismProperty.monomorphisms _).of_isPushout h hl

end Mono

instance preservesMonomorphisms_Loc : Loc.{u}.PreservesMonomorphisms where
  preserves {X X'} f _ := by
    have e : f = MarkedPresheaf.homMk (Y := MarkedPresheaf.ofMarking _ (imageMarking f))
        (MarkedPresheaf.forget.map f) (fun V x hx =>
          (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 (Or.inl ⟨x, hx, rfl⟩)) ≫
        MarkedPresheaf.homMk (X := MarkedPresheaf.ofMarking _ (imageMarking f)) (Y := X') (𝟙 _)
          (fun V _ hy => marked_of_mem_imageMarking f
            ((MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hy)) :=
      MarkedPresheaf.hom_ext rfl
    rw [e, Functor.map_comp]
    have := mono_loc_map_imageMarking f
    have := mono_loc_map_toMarking f
    exact mono_comp _ _

theorem nonempty_isColimit_Loc_mapCocone {J : Type u} [SmallCategory J]
    {K : J ⥤ MarkedDiagSet.{u}}
    {c : Cocone K} (hc : IsColimit c)
    (h : ∀ (a : Atom) (ha : atomMarking.markable a),
      IsColimit (((evaluation _ (Type u)).obj (op (MarkedSite.marked a ha))).mapCocone
        ((ObjectProperty.ι _).mapCocone c))) :
    Nonempty (IsColimit (Loc.mapCocone c)) := by
  have : PreservesColimitsOfSize.{u, u} (MarkedPresheaf.forget.{u, 0} (D := atomMarking)) :=
    (MarkedPresheaf.forgetSharpAdjunction atomMarking).leftAdjoint_preservesColimits
  refine MarkedPresheaf.isColimit_extend_mapCocone locSite (c := c)
    (evaluationJointlyReflectsColimits _ fun ⟨a, b, hb⟩ => ?_)
  cases b
  · exact isColimitOfPreserves ((evaluation _ (Type u)).obj (op a))
      (isColimitOfPreserves MarkedPresheaf.forget hc)
  · exact h a (hb rfl)

private theorem isSeparated_coprod (A B : MarkedDiagSet.{u}) :
    Presieve.IsSeparated (MarkedSite.topology atomMarking)
      (FunctorToTypes.coprod A.obj B.obj) :=
  MarkedSite.isSeparated_iff.2 fun x => by
    rintro (s | s) (t | t) h
    · exact congrArg Sum.inl (A.injective_map_toSelf x (Sum.inl_injective h))
    · exact (Sum.inl_ne_inr h).elim
    · exact (Sum.inr_ne_inl h).elim
    · exact congrArg Sum.inr (B.injective_map_toSelf x (Sum.inr_injective h))

private def coprodCofan (A B : MarkedDiagSet.{u}) : BinaryCofan A B :=
  BinaryCofan.mk (P := ⟨_, isSeparated_coprod A B⟩)
    (ObjectProperty.homMk FunctorToTypes.coprod.inl)
    (ObjectProperty.homMk FunctorToTypes.coprod.inr)

private def isColimitιMapCoconeCoprodCofan (A B : MarkedDiagSet.{u}) :
    IsColimit ((ObjectProperty.ι _).mapCocone (coprodCofan A B)) :=
  (isColimitMapCoconeBinaryCofanEquiv (ObjectProperty.ι _) _ _).symm
    (FunctorToTypes.binaryCoproductColimit A.obj B.obj)

instance preservesColimit_pair_Loc (A B : MarkedDiagSet.{u}) : PreservesColimit (pair A B) Loc :=
  preservesColimit_of_preserves_colimit_cocone
    (isColimitOfReflects (ObjectProperty.ι _) (isColimitιMapCoconeCoprodCofan A B))
    (MarkedPresheaf.isColimit_extend_mapCocone locSite (isColimitιMapCoconeCoprodCofan A B)).some

end Atoms.Diagrammatic

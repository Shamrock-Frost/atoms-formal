import Mathlib.CategoryTheory.Bicategory.Coherence
import Mathlib.Combinatorics.Quiver.Cast
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

namespace CategoryTheory

universe w v u v₁ u₁ v₂ u₂

variable {B : Type u} [Bicategory.{w, v} B] {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂}
  [Quiver.{v₂} W]

namespace FreeBicategory

open Bicategory

theorem lift_map₂_eq (F : Prefunctor V B) {x y : FreeBicategory V} {p q : x ⟶ y}
    (η θ : p ⟶ q) : (lift F).map₂ η = (lift F).map₂ θ :=
  congrArg (lift F).map₂ (Subsingleton.elim η θ)

theorem lift_map_lift (G : Prefunctor V (FreeBicategory W)) (F : Prefunctor W B)
    {a b : FreeBicategory V} (f : a ⟶ b) :
    (lift (G ⋙q (lift F).toPrefunctor)).map f = (lift F).map ((lift G).map f) := by
  induction f with
  | of f => rfl
  | id a => rfl
  | comp f g ihf ihg => exact congrArg₂ (· ≫ ·) ihf ihg

theorem lift_map₂_whiskerLeft (F : Prefunctor W B) {a b c : FreeBicategory W} (f : a ⟶ b)
    {g h : b ⟶ c} (η : g ⟶ h) : (lift F).map₂ (f ◁ η) = (lift F).map f ◁ (lift F).map₂ η := by
  induction η using Quot.ind
  rfl

theorem lift_map₂_whiskerRight (F : Prefunctor W B) {a b c : FreeBicategory W} {f g : a ⟶ b}
    (η : f ⟶ g) (h : b ⟶ c) : (lift F).map₂ (η ▷ h) = (lift F).map₂ η ▷ (lift F).map h := by
  induction η using Quot.ind
  rfl

section Conj

variable {a b c d : B}

private theorem conj_id {f f' : a ⟶ b} (hf : f = f') :
    𝟙 f = eqToHom hf ≫ 𝟙 f' ≫ eqToHom hf.symm := by
  subst hf
  simp

private theorem conj_comp {f f' g g' h h' : a ⟶ b} (hf : f = f') (hg : g = g') (hh : h = h')
    {φ : f ⟶ g} {ψ : g ⟶ h} {φ' : f' ⟶ g'} {ψ' : g' ⟶ h'}
    (h₁ : φ = eqToHom hf ≫ φ' ≫ eqToHom hg.symm) (h₂ : ψ = eqToHom hg ≫ ψ' ≫ eqToHom hh.symm) :
    φ ≫ ψ = eqToHom hf ≫ (φ' ≫ ψ') ≫ eqToHom hh.symm := by
  subst hf hg hh h₁ h₂
  simp

private theorem conj_whiskerLeft {f f' : a ⟶ b} {g g' h h' : b ⟶ c} (hf : f = f') (hg : g = g')
    (hh : h = h') {η : g ⟶ h} {η' : g' ⟶ h'} (hη : η = eqToHom hg ≫ η' ≫ eqToHom hh.symm) :
    f ◁ η = eqToHom (by rw [hf, hg]) ≫ f' ◁ η' ≫ eqToHom (by rw [hf, hh]) := by
  subst hf hg hh hη
  simp

private theorem conj_whiskerRight {f f' g g' : a ⟶ b} {h h' : b ⟶ c} (hf : f = f') (hg : g = g')
    (hh : h = h') {η : f ⟶ g} {η' : f' ⟶ g'} (hη : η = eqToHom hf ≫ η' ≫ eqToHom hg.symm) :
    η ▷ h = eqToHom (by rw [hf, hh]) ≫ η' ▷ h' ≫ eqToHom (by rw [hg, hh]) := by
  subst hf hg hh hη
  simp

private theorem conj_associator {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d} (hf : f = f')
    (hg : g = g') (hh : h = h') :
    (α_ f g h).hom = eqToHom (by rw [hf, hg, hh]) ≫ (α_ f' g' h').hom ≫
      eqToHom (by rw [hf, hg, hh]) ∧
    (α_ f g h).inv = eqToHom (by rw [hf, hg, hh]) ≫ (α_ f' g' h').inv ≫
      eqToHom (by rw [hf, hg, hh]) := by
  subst hf hg hh
  simp

private theorem conj_unitors {f f' : a ⟶ b} (hf : f = f') :
    ((λ_ f).hom = eqToHom (by rw [hf]) ≫ (λ_ f').hom ≫ eqToHom hf.symm ∧
      (λ_ f).inv = eqToHom hf ≫ (λ_ f').inv ≫ eqToHom (by rw [hf])) ∧
    ((ρ_ f).hom = eqToHom (by rw [hf]) ≫ (ρ_ f').hom ≫ eqToHom hf.symm ∧
      (ρ_ f).inv = eqToHom hf ≫ (ρ_ f').inv ≫ eqToHom (by rw [hf])) := by
  subst hf
  simp

end Conj

theorem lift_map₂_lift (G : Prefunctor V (FreeBicategory W)) (F : Prefunctor W B)
    {a b : FreeBicategory V} {f g : a ⟶ b} (η : f ⟶ g) :
    (lift (G ⋙q (lift F).toPrefunctor)).map₂ η = eqToHom (lift_map_lift G F f) ≫
      (lift F).map₂ ((lift G).map₂ η) ≫ eqToHom (lift_map_lift G F g).symm := by
  induction η using Quot.ind with | mk η => ?_
  induction η with
  | id f => exact conj_id _
  | vcomp η θ ihη ihθ =>
    exact (conj_comp _ _ (lift_map_lift G F _) ihη ihθ).trans
      (congrArg (fun z => eqToHom _ ≫ z ≫ eqToHom _) ((lift F).map₂_comp _ _).symm)
  | whisker_left f η ih =>
    exact (conj_whiskerLeft (lift_map_lift G F f) (lift_map_lift G F _) (lift_map_lift G F _)
      ih).trans
      (congrArg (fun z => eqToHom _ ≫ z ≫ eqToHom _) (lift_map₂_whiskerLeft F _ _).symm)
  | whisker_right h η ih =>
    exact (conj_whiskerRight (lift_map_lift G F _) (lift_map_lift G F _) (lift_map_lift G F h)
      ih).trans
      (congrArg (fun z => eqToHom _ ≫ z ≫ eqToHom _) (lift_map₂_whiskerRight F _ _).symm)
  | associator f g h =>
    exact (conj_associator (lift_map_lift G F f) (lift_map_lift G F g) (lift_map_lift G F h)).1
  | associator_inv f g h =>
    exact (conj_associator (lift_map_lift G F f) (lift_map_lift G F g) (lift_map_lift G F h)).2
  | right_unitor f => exact (conj_unitors (lift_map_lift G F f)).2.1
  | right_unitor_inv f => exact (conj_unitors (lift_map_lift G F f)).2.2
  | left_unitor f => exact (conj_unitors (lift_map_lift G F f)).1.1
  | left_unitor_inv f => exact (conj_unitors (lift_map_lift G F f)).1.2

theorem lift_map₂_eq_eqToHom (F : Prefunctor W B) {x y : FreeBicategory W} {p q : x ⟶ y}
    (η : p ⟶ q) (h : p = q) : (lift F).map₂ η = eqToHom (congrArg (lift F).map h) := by
  subst h
  rw [Subsingleton.elim η (𝟙 p), PrelaxFunctor.map₂_id, eqToHom_refl]

theorem normalizeAux_nil_inclusionPathAux {a : W} :
    ∀ {b : W} (p : Quiver.Path a b), normalizeAux Quiver.Path.nil (inclusionPathAux p) = p
  | _, .nil => rfl
  | _, .cons p e => congrArg (·.cons e) (normalizeAux_nil_inclusionPathAux p)

theorem normalizeAux_homOfEq_id {a b c : FreeBicategory W} (p : Quiver.Path (V := W) a b)
    (h : b = c) :
    normalizeAux p (Quiver.homOfEq (𝟙 b) rfl h) = Quiver.Path.cast (U := W) rfl h p := by
  subst h
  rfl

def homOfNormalizeAuxEq {a b : FreeBicategory W} {f g : a ⟶ b}
    (h : normalizeAux Quiver.Path.nil f = normalizeAux Quiver.Path.nil g) : f ⟶ g :=
  (λ_ f).inv ≫ (normalizeIso Quiver.Path.nil f).hom ≫
    eqToHom (congrArg (fun p => (preinclusion W).map ⟨p⟩) h) ≫
      (normalizeIso Quiver.Path.nil g).inv ≫ (λ_ g).hom

end FreeBicategory

namespace Bicategory

open Quiver (Path)

def pathPseudofunctor (F : Prefunctor V B) : LocallyDiscrete (Paths V) ⥤ᵖ B :=
  (FreeBicategory.inclusion V).comp (FreeBicategory.lift F)

def pathComp (F : Prefunctor V B) {x y : V} (p : Path x y) : F.obj x ⟶ F.obj y :=
  (pathPseudofunctor F).map (Quiver.Hom.toLoc (C := Paths V) p)

@[simp]
theorem pathComp_nil (F : Prefunctor V B) (x : V) :
    pathComp F (Path.nil : Path x x) = 𝟙 (F.obj x) :=
  rfl

@[simp]
theorem pathComp_cons (F : Prefunctor V B) {x y z : V} (p : Path x y) (e : y ⟶ z) :
    pathComp F (p.cons e) = pathComp F p ≫ F.map e :=
  rfl

def pathCompCompIso (F : Prefunctor V B) {x y z : V} (p : Path x y) (q : Path y z) :
    pathComp F (p.comp q) ≅ pathComp F p ≫ pathComp F q :=
  (pathPseudofunctor F).mapComp (Quiver.Hom.toLoc (C := Paths V) p)
    (Quiver.Hom.toLoc (C := Paths V) q)

theorem pathCompCompIso_comp_nil (F : Prefunctor V B) {x y : V} (p : Path x y) :
    pathCompCompIso F p Path.nil = (ρ_ (pathComp F p)).symm :=
  Iso.ext (Category.comp_id _)

theorem pathCompCompIso_nil_comp (F : Prefunctor V B) {x y : V} (q : Path x y) :
    (pathCompCompIso F Path.nil q).hom ≫ (λ_ (pathComp F q)).hom =
      eqToHom (congrArg (pathComp F) (Path.nil_comp q)) := by
  have h := (pathPseudofunctor F).map₂_left_unitor (Quiver.Hom.toLoc (C := Paths V) q)
  refine Eq.trans ?_ (((pathPseudofunctor F).map₂_eqToHom _ _
    (Discrete.ext (Path.nil_comp q))).symm.trans h).symm
  have hid : ((pathPseudofunctor F).mapId (⟨x⟩ : LocallyDiscrete (Paths V))).hom = 𝟙 _ :=
    (Category.comp_id _).trans ((FreeBicategory.lift F).map₂_id _)
  refine congrArg (_ ≫ ·) ?_
  rw [hid]
  exact ((congrArg (· ≫ _) (id_whiskerRight _ _)).trans (Category.id_comp _)).symm

theorem pathCompCompIso_nil_whiskerLeft_heq (F : Prefunctor V B) {x y : V}
    {q q' : Quiver.Path x y} (ζ : pathComp F q ⟶ pathComp F q') :
    (pathCompCompIso F .nil q).hom ≫ pathComp F .nil ◁ ζ ≫ (pathCompCompIso F .nil q').inv ≍ ζ := by
  have h₁ (q : Quiver.Path x y) : (pathCompCompIso F .nil q).hom =
      eqToHom (congrArg (pathComp F) (Quiver.Path.nil_comp q)) ≫ (λ_ (pathComp F q)).inv := by
    rw [← pathCompCompIso_nil_comp]
    simp
  have h₂ : (pathCompCompIso F .nil q').inv =
      (λ_ (pathComp F q')).hom ≫ eqToHom (congrArg (pathComp F) (Quiver.Path.nil_comp q')).symm :=
    Iso.inv_ext (by rw [h₁ q']; simp)
  rw [h₁ q, h₂]
  simp only [pathComp_nil, Category.assoc, Iso.inv_hom_id_assoc, id_whiskerLeft,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

@[reassoc]
theorem pathCompCompIso_assoc (F : Prefunctor V B) {x y z w : V} (p : Path x y) (q : Path y z)
    (r : Path z w) :
    (pathCompCompIso F (p.comp q) r).hom ≫ (pathCompCompIso F p q).hom ▷ pathComp F r =
      eqToHom (congrArg (pathComp F) (Path.comp_assoc p q r)) ≫
        (pathCompCompIso F p (q.comp r)).hom ≫ pathComp F p ◁ (pathCompCompIso F q r).hom ≫
          (α_ _ _ _).inv :=
  ((pathPseudofunctor F).mapComp_assoc_left_hom (Quiver.Hom.toLoc (C := Paths V) p)
    (Quiver.Hom.toLoc (C := Paths V) q) (Quiver.Hom.toLoc (C := Paths V) r)).trans
      (congrArg (· ≫ _) ((pathPseudofunctor F).map₂_eqToHom _ _
        (Discrete.ext (Path.comp_assoc p q r))))

@[reassoc]
theorem pathCompCompIso_assoc_inv (F : Prefunctor V B) {x y z w : V} (p : Path x y)
    (q : Path y z) (r : Path z w) :
    (pathCompCompIso F p q).inv ▷ pathComp F r ≫ (pathCompCompIso F (p.comp q) r).inv =
      (α_ _ _ _).hom ≫ pathComp F p ◁ (pathCompCompIso F q r).inv ≫
        (pathCompCompIso F p (q.comp r)).inv ≫
          eqToHom (congrArg (pathComp F) (Path.comp_assoc p q r).symm) := by
  have h : pathCompCompIso F (p.comp q) r ≪≫ whiskerRightIso (pathCompCompIso F p q) _ =
      eqToIso (congrArg (pathComp F) (Path.comp_assoc p q r)) ≪≫ pathCompCompIso F p (q.comp r) ≪≫
        whiskerLeftIso _ (pathCompCompIso F q r) ≪≫ (α_ _ _ _).symm :=
    Iso.ext (by simpa using pathCompCompIso_assoc F p q r)
  simpa using congrArg Iso.inv h

@[reassoc]
theorem eqToHom_pathCompCompIso_hom (F : Prefunctor V B) {x y z : V} (p : Path x y)
    {q q' : Path y z} (h : q = q') :
    eqToHom (congrArg (pathComp F) (congrArg p.comp h)) ≫ (pathCompCompIso F p q').hom =
      (pathCompCompIso F p q).hom ≫ pathComp F p ◁ eqToHom (congrArg (pathComp F) h) := by
  subst h
  simp

@[reassoc]
theorem whiskerLeft_eqToHom_pathCompCompIso_inv (F : Prefunctor V B) {x y z : V} (p : Path x y)
    {q q' : Path y z} (h : q = q') :
    pathComp F p ◁ eqToHom (congrArg (pathComp F) h) ≫ (pathCompCompIso F p q').inv =
      (pathCompCompIso F p q).inv ≫ eqToHom (congrArg (pathComp F) (congrArg p.comp h)) := by
  subst h
  simp

@[reassoc]
theorem pathCompCompIso_hom_eqToHom_whiskerRight (F : Prefunctor V B) {x y z : V}
    {p p' : Path x y} (h : p = p') (q : Path y z) :
    (pathCompCompIso F p q).hom ≫ eqToHom (congrArg (pathComp F) h) ▷ pathComp F q =
      eqToHom (congrArg (pathComp F) (congrArg (·.comp q) h)) ≫ (pathCompCompIso F p' q).hom := by
  subst h
  simp

@[reassoc]
theorem eqToHom_whiskerRight_pathCompCompIso_inv (F : Prefunctor V B) {x y z : V}
    {p p' : Path x y} (h : p = p') (q : Path y z) :
    eqToHom (congrArg (pathComp F) h) ▷ pathComp F q ≫ (pathCompCompIso F p' q).inv =
      (pathCompCompIso F p q).inv ≫ eqToHom (congrArg (pathComp F) (congrArg (·.comp q) h)) := by
  subst h
  simp

@[reassoc]
theorem pathCompCompIso_inv_eqToHom_hom (F : Prefunctor V B) {x y z : V} {p p' : Path x y}
    {q q' : Path y z} (hp : p = p') (hq : q = q') (h : p.comp q = p'.comp q') :
    (pathCompCompIso F p q).inv ≫ eqToHom (congrArg (pathComp F) h) ≫
        (pathCompCompIso F p' q').hom =
      eqToHom (by rw [hp, hq]) := by
  subst hp hq
  simp

def pathWhisker (F : Prefunctor V B) {x y z w : V} (p : Path x y) {q q' : Path y z}
    (η : pathComp F q ⟶ pathComp F q') (r : Path z w) :
    pathComp F (p.comp (q.comp r)) ⟶ pathComp F (p.comp (q'.comp r)) :=
  (pathCompCompIso F p (q.comp r)).hom ≫
    pathComp F p ◁ ((pathCompCompIso F q r).hom ≫ η ▷ pathComp F r ≫
      (pathCompCompIso F q' r).inv) ≫ (pathCompCompIso F p (q'.comp r)).inv

theorem pathWhisker_id (G : Prefunctor V B) {a b c d : V}
    (P : Quiver.Path a b) (Q : Quiver.Path b c) (R : Quiver.Path c d) :
    pathWhisker G P (𝟙 (pathComp G Q)) R = 𝟙 _ := by
  simp only [pathWhisker, id_whiskerRight, Category.id_comp, Iso.hom_inv_id, whiskerLeft_id]

theorem pathWhisker_nil_nil (F : Prefunctor V B) {x y : V} {q q' : Path x y}
    (η : pathComp F q ⟶ pathComp F q') :
    pathWhisker F Path.nil η Path.nil =
      eqToHom (congrArg (pathComp F) (Path.nil_comp q)) ≫ η ≫
        eqToHom (congrArg (pathComp F) (Path.nil_comp q').symm) := by
  have h₁ (q : Path x y) : (pathCompCompIso F Path.nil q).hom =
      eqToHom (congrArg (pathComp F) (Path.nil_comp q)) ≫ (λ_ (pathComp F q)).inv := by
    rw [← pathCompCompIso_nil_comp]
    simp
  have h₂ (q : Path x y) : (pathCompCompIso F Path.nil q).inv =
      (λ_ (pathComp F q)).hom ≫ eqToHom (congrArg (pathComp F) (Path.nil_comp q).symm) :=
    Iso.inv_ext (by rw [h₁]; simp)
  rw [pathWhisker, h₁ (q.comp Path.nil), h₂ (q'.comp Path.nil), pathCompCompIso_comp_nil,
    pathCompCompIso_comp_nil]
  simp only [Iso.symm_hom, Iso.symm_inv, pathComp_nil, Category.assoc]
  congr 1
  bicategory

theorem pathWhisker_comp_left (F : Prefunctor V B) {x y y' z w : V} (p : Path x y)
    (p' : Path y y') {q q' : Path y' z} (η : pathComp F q ⟶ pathComp F q') (r : Path z w) :
    pathWhisker F (p.comp p') η r =
      eqToHom (congrArg (pathComp F) (Path.comp_assoc p p' (q.comp r))) ≫
        (pathCompCompIso F p (p'.comp (q.comp r))).hom ≫ pathComp F p ◁ pathWhisker F p' η r ≫
          (pathCompCompIso F p (p'.comp (q'.comp r))).inv ≫
            eqToHom (congrArg (pathComp F) (Path.comp_assoc p p' (q'.comp r)).symm) := by
  have e₁ : (pathCompCompIso F (p.comp p') (q.comp r)).hom =
      eqToHom (congrArg (pathComp F) (Path.comp_assoc p p' (q.comp r))) ≫
        (pathCompCompIso F p (p'.comp (q.comp r))).hom ≫
          pathComp F p ◁ (pathCompCompIso F p' (q.comp r)).hom ≫ (α_ _ _ _).inv ≫
            (pathCompCompIso F p p').inv ▷ _ := by
    rw [← reassoc_of% (pathCompCompIso_assoc F p p' (q.comp r))]
    simp
  have e₂ : (pathCompCompIso F (p.comp p') (q'.comp r)).inv =
      (pathCompCompIso F p p').hom ▷ _ ≫ (α_ _ _ _).hom ≫
        pathComp F p ◁ (pathCompCompIso F p' (q'.comp r)).inv ≫
          (pathCompCompIso F p (p'.comp (q'.comp r))).inv ≫
          eqToHom (congrArg (pathComp F) (Path.comp_assoc p p' (q'.comp r)).symm) := by
    rw [← pathCompCompIso_assoc_inv]
    simp
  rw [pathWhisker, e₁, e₂, pathWhisker]
  simp only [Category.assoc, whiskerLeft_comp]
  congr 3
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, ← whisker_exchange_assoc,
    inv_hom_whiskerRight_assoc]
  bicategory

@[reassoc]
private theorem pathCompCompIso_whiskerRight_whiskerLeft (F : Prefunctor V B) {x y z w : V}
    (p : Path x y)
    {X X' : Path y z} (θ : pathComp F X ⟶ pathComp F X') (r : Path z w) :
    (pathCompCompIso F (p.comp X) r).hom ≫
        ((pathCompCompIso F p X).hom ≫ pathComp F p ◁ θ ≫ (pathCompCompIso F p X').inv) ▷
          pathComp F r ≫ (pathCompCompIso F (p.comp X') r).inv =
      eqToHom (congrArg (pathComp F) (Path.comp_assoc p X r)) ≫
        (pathCompCompIso F p (X.comp r)).hom ≫
          pathComp F p ◁ ((pathCompCompIso F X r).hom ≫ θ ▷ pathComp F r ≫
            (pathCompCompIso F X' r).inv) ≫ (pathCompCompIso F p (X'.comp r)).inv ≫
              eqToHom (congrArg (pathComp F) (Path.comp_assoc p X' r).symm) := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [pathCompCompIso_assoc_assoc, pathCompCompIso_assoc_inv]
  simp [whisker_assoc]

private theorem pathCompCompIso_whiskerRight_whiskerRight (F : Prefunctor V B) {x y z w : V}
    {q q' : Path x y} (η : pathComp F q ⟶ pathComp F q') (r : Path y z) (r' : Path z w) :
    (pathCompCompIso F (q.comp r) r').hom ≫
        ((pathCompCompIso F q r).hom ≫ η ▷ pathComp F r ≫ (pathCompCompIso F q' r).inv) ▷
          pathComp F r' ≫ (pathCompCompIso F (q'.comp r) r').inv =
      eqToHom (congrArg (pathComp F) (Path.comp_assoc q r r')) ≫
        (pathCompCompIso F q (r.comp r')).hom ≫ η ▷ pathComp F (r.comp r') ≫
          (pathCompCompIso F q' (r.comp r')).inv ≫
            eqToHom (congrArg (pathComp F) (Path.comp_assoc q' r r').symm) := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [pathCompCompIso_assoc_assoc, pathCompCompIso_assoc_inv]
  congr 2
  rw [← whiskerRight_comp_assoc, whisker_exchange_assoc, ← whiskerLeft_comp_assoc]
  simp

theorem pathWhisker_comp_right (F : Prefunctor V B) {x y z w w' : V} (p : Path x y)
    {q q' : Path y z} (η : pathComp F q ⟶ pathComp F q') (r : Path z w) (r' : Path w w') :
    pathWhisker F p η (r.comp r') =
      eqToHom (congrArg (pathComp F) (by simp only [Path.comp_assoc])) ≫
        (pathCompCompIso F (p.comp (q.comp r)) r').hom ≫ pathWhisker F p η r ▷ pathComp F r' ≫
          (pathCompCompIso F (p.comp (q'.comp r)) r').inv ≫
            eqToHom (congrArg (pathComp F) (by simp only [Path.comp_assoc])) := by
  conv_rhs => rw [pathWhisker]
  rw [pathCompCompIso_whiskerRight_whiskerLeft_assoc,
    pathCompCompIso_whiskerRight_whiskerRight]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← eqToHom_pathCompCompIso_hom_assoc F p (Path.comp_assoc q r r'),
    whiskerLeft_eqToHom_pathCompCompIso_inv_assoc F p (Path.comp_assoc q' r r').symm]
  simp only [eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
    Category.comp_id, pathWhisker, whiskerLeft_comp, Category.assoc]

@[reassoc]
theorem pathWhisker_exchange (F : Prefunctor V B) {a b c d e f : V} (p : Path a b)
    {q₁ q₁' : Path b c} (η₁ : pathComp F q₁ ⟶ pathComp F q₁') (m : Path c d) {q₂ q₂' : Path d e}
    (η₂ : pathComp F q₂ ⟶ pathComp F q₂') (r : Path e f) :
    pathWhisker F p η₁ (m.comp (q₂.comp r)) ≫
        eqToHom (congrArg (pathComp F) (by simp only [Path.comp_assoc])) ≫
          pathWhisker F (p.comp (q₁'.comp m)) η₂ r =
      eqToHom (congrArg (pathComp F) (by simp only [Path.comp_assoc])) ≫
        pathWhisker F (p.comp (q₁.comp m)) η₂ r ≫
          eqToHom (congrArg (pathComp F) (by simp only [Path.comp_assoc])) ≫
            pathWhisker F p η₁ (m.comp (q₂'.comp r)) ≫
              eqToHom (congrArg (pathComp F) (by simp only [Path.comp_assoc])) := by
  rw [pathWhisker_comp_left F p (q₁'.comp m), pathWhisker_comp_left F q₁' m,
    pathWhisker_comp_left F p (q₁.comp m), pathWhisker_comp_left F q₁ m]
  simp only [pathWhisker, whiskerLeft_comp, Category.assoc, eqToHom_trans_assoc]
  rw [eqToHom_pathCompCompIso_hom_assoc F p (Path.comp_assoc q₁' m (q₂.comp r)).symm,
    whiskerLeft_eqToHom_pathCompCompIso_inv_assoc F p (Path.comp_assoc q₁' m (q₂'.comp r)).symm,
    eqToHom_pathCompCompIso_hom_assoc F p (Path.comp_assoc q₁ m (q₂.comp r)).symm,
    whiskerLeft_eqToHom_pathCompCompIso_inv_assoc F p (Path.comp_assoc q₁ m (q₂'.comp r)).symm]
  simp only [eqToHom_trans, eqToHom_trans_assoc, Iso.inv_hom_id_assoc, eqToHom_refl,
    Category.id_comp, ← whiskerLeft_comp_assoc]
  rw [← whisker_exchange_assoc]

section Lift

open FreeBicategory

theorem pathComp_of {a : W} :
    ∀ {b : W} (p : Path a b), pathComp FreeBicategory.of p = inclusionPathAux p
  | _, .nil => rfl
  | _, .cons p e => congrArg (· ≫ Hom.of e) (pathComp_of p)

theorem pathComp_comp_lift (G : Prefunctor V (FreeBicategory W)) (F : Prefunctor W B) {x y : V}
    (p : Path x y) :
    pathComp (G ⋙q (lift F).toPrefunctor) p = (lift F).map (pathComp G p) :=
  lift_map_lift G F _

theorem pathCompCompIso_comp_lift (G : Prefunctor V (FreeBicategory W)) (F : Prefunctor W B)
    {x y z : V} (p : Path x y) (q : Path y z) :
    (pathCompCompIso (G ⋙q (lift F).toPrefunctor) p q).hom =
      eqToHom (pathComp_comp_lift G F (p.comp q)) ≫ (lift F).map₂ (pathCompCompIso G p q).hom ≫
        eqToHom (congrArg₂ (· ≫ ·) (pathComp_comp_lift G F p) (pathComp_comp_lift G F q)).symm := by
  have hH : (pathCompCompIso (G ⋙q (lift F).toPrefunctor) p q).hom =
      (lift (G ⋙q (lift F).toPrefunctor)).map₂ ((inclusion V).mapComp (Quiver.Hom.toLoc p)
        (Quiver.Hom.toLoc q)).hom ≫ 𝟙 _ := rfl
  have hG : (pathCompCompIso G p q).hom = (lift G).map₂ ((inclusion V).mapComp
      (Quiver.Hom.toLoc p) (Quiver.Hom.toLoc q)).hom ≫ 𝟙 _ := rfl
  rw [hH, hG, Category.comp_id, Category.comp_id]
  exact lift_map₂_lift G F _

theorem pathCompCompIso_comp_lift_inv (G : Prefunctor V (FreeBicategory W)) (F : Prefunctor W B)
    {x y z : V} (p : Path x y) (q : Path y z) :
    (pathCompCompIso (G ⋙q (lift F).toPrefunctor) p q).inv =
      eqToHom (congrArg₂ (· ≫ ·) (pathComp_comp_lift G F p) (pathComp_comp_lift G F q)) ≫
        (lift F).map₂ (pathCompCompIso G p q).inv ≫
          eqToHom (pathComp_comp_lift G F (p.comp q)).symm := by
  have hH : (pathCompCompIso (G ⋙q (lift F).toPrefunctor) p q).inv =
      𝟙 _ ≫ (lift (G ⋙q (lift F).toPrefunctor)).map₂ ((inclusion V).mapComp (Quiver.Hom.toLoc p)
        (Quiver.Hom.toLoc q)).inv := rfl
  have hG : (pathCompCompIso G p q).inv = 𝟙 _ ≫ (lift G).map₂ ((inclusion V).mapComp
      (Quiver.Hom.toLoc p) (Quiver.Hom.toLoc q)).inv := rfl
  rw [hH, hG, Category.id_comp, Category.id_comp]
  exact lift_map₂_lift G F _

theorem pathCompCompIso_cons_hom (F : Prefunctor V B) {x y z w : V} (P : Quiver.Path x y)
    (Q : Quiver.Path y z) (e : z ⟶ w) :
    (pathCompCompIso F P (Q.cons e)).hom = (pathCompCompIso F P Q).hom ▷ F.map e ≫
      (α_ _ _ _).hom := by
  have h₁ : (pathCompCompIso F P (Q.cons e)).hom =
      (lift F).map₂ ((inclusionMapCompAux P Q).hom ▷ Hom.of e) ≫
        (lift F).map₂ (α_ ((preinclusion V).map ⟨P⟩) ((preinclusion V).map ⟨Q⟩)
          (Hom.of e : FreeBicategory.of.obj z ⟶ FreeBicategory.of.obj w)).hom := by
    change (lift F).map₂ (inclusionMapCompAux P (Q.cons e)).hom ≫ 𝟙 _ = _
    rw [Category.comp_id, inclusionMapCompAux]
    exact PrelaxFunctor.map₂_comp (lift F).toPrelaxFunctor _ _
  have h₂ : (pathCompCompIso F P Q).hom = (lift F).map₂ (inclusionMapCompAux P Q).hom ≫ 𝟙 _ := rfl
  rw [h₁, h₂, Category.comp_id]
  exact congrArg (· ≫ _) (lift_map₂_whiskerRight F (inclusionMapCompAux P Q).hom (Hom.of e))

theorem nf_pathComp_comp (G : Prefunctor V (FreeBicategory W)) {a b c : V} (P : Quiver.Path a b)
    (Q : Quiver.Path b c) :
    normalizeAux .nil (pathComp G (P.comp Q)) =
      (normalizeAux .nil (pathComp G P)).comp (normalizeAux .nil (pathComp G Q)) :=
  (normalizeAux_congr _ (pathCompCompIso G P Q).hom).trans (normalizeAux_nil_comp _ _)

section Conj
variable {a b c : B}

private theorem conj_whiskerRight_conj {Q Q' S S' : a ⟶ b} {R R' : b ⟶ c} {X X' Y Y' : a ⟶ c}
    (hQ : Q = Q') (hS : S = S') (hR : R = R') (hX : X = X') (hY : Y = Y') {Ψ : X ⟶ Q ≫ R}
    {Ψ' : X' ⟶ Q' ≫ R'} (hΨ : Ψ = eqToHom hX ≫ Ψ' ≫ eqToHom (by rw [hQ, hR])) (η' : Q' ⟶ S')
    {Ψ₂ : S ≫ R ⟶ Y} {Ψ₂' : S' ≫ R' ⟶ Y'}
    (hΨ₂ : Ψ₂ = eqToHom (by rw [hS, hR]) ≫ Ψ₂' ≫ eqToHom hY.symm) :
    Ψ ≫ (eqToHom hQ ≫ η' ≫ eqToHom hS.symm) ▷ R ≫ Ψ₂ =
      eqToHom hX ≫ (Ψ' ≫ η' ▷ R' ≫ Ψ₂') ≫ eqToHom hY.symm := by
  subst hQ hS hR hX hY hΨ hΨ₂
  simp

private theorem conj_whiskerLeft_conj {P P' : a ⟶ b} {X X' Y Y' : b ⟶ c} {Z Z' T T' : a ⟶ c}
    (hP : P = P') (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (hT : T = T') {Φ : Z ⟶ P ≫ X}
    {Φ' : Z' ⟶ P' ≫ X'} (hΦ : Φ = eqToHom hZ ≫ Φ' ≫ eqToHom (by rw [hP, hX])) {Θ : X ⟶ Y}
    {Θ' : X' ⟶ Y'} (hΘ : Θ = eqToHom hX ≫ Θ' ≫ eqToHom hY.symm) {Ψ : P ≫ Y ⟶ T}
    {Ψ' : P' ≫ Y' ⟶ T'} (hΨ : Ψ = eqToHom (by rw [hP, hY]) ≫ Ψ' ≫ eqToHom hT.symm) :
    Φ ≫ P ◁ Θ ≫ Ψ = eqToHom hZ ≫ (Φ' ≫ P' ◁ Θ' ≫ Ψ') ≫ eqToHom hT.symm := by
  subst hP hX hY hZ hT hΦ hΘ hΨ
  simp

end Conj

theorem pathWhisker_comp_lift (G : Prefunctor V (FreeBicategory W)) (F : Prefunctor W B)
    {x y z w : V} (p : Path x y) {q q' : Path y z}
    (η : (lift F).map (pathComp G q) ⟶ (lift F).map (pathComp G q')) (r : Path z w) :
    pathWhisker (G ⋙q (lift F).toPrefunctor) p
        (eqToHom (pathComp_comp_lift G F q) ≫ η ≫ eqToHom (pathComp_comp_lift G F q').symm) r =
      eqToHom (pathComp_comp_lift G F _) ≫
        ((lift F).map₂ (pathCompCompIso G p (q.comp r)).hom ≫
          (lift F).map (pathComp G p) ◁ ((lift F).map₂ (pathCompCompIso G q r).hom ≫
            η ▷ (lift F).map (pathComp G r) ≫ (lift F).map₂ (pathCompCompIso G q' r).inv) ≫
          (lift F).map₂ (pathCompCompIso G p (q'.comp r)).inv) ≫
        eqToHom (pathComp_comp_lift G F _).symm :=
  conj_whiskerLeft_conj (pathComp_comp_lift G F p) (pathComp_comp_lift G F _)
    (pathComp_comp_lift G F _) (pathComp_comp_lift G F _) (pathComp_comp_lift G F _)
    (pathCompCompIso_comp_lift G F _ _)
    (conj_whiskerRight_conj (pathComp_comp_lift G F q) (pathComp_comp_lift G F q')
      (pathComp_comp_lift G F r) (pathComp_comp_lift G F _) (pathComp_comp_lift G F _)
      (pathCompCompIso_comp_lift G F _ _) η (pathCompCompIso_comp_lift_inv G F _ _))
    (pathCompCompIso_comp_lift_inv G F _ _)

end Lift

section PathCell

structure PathCell (B : Type u) [Bicategory.{w, v} B] where
  src : B
  tgt : B
  dom : Path (V := B) src tgt
  cod : Path (V := B) src tgt
  hom : pathComp (𝟭q B) dom ⟶ pathComp (𝟭q B) cod

theorem PathCell.ext {c c' : PathCell B} (hsrc : c.src = c'.src) (htgt : c.tgt = c'.tgt)
    (hdom : c.dom ≍ c'.dom) (hcod : c.cod ≍ c'.cod) (hhom : c.hom ≍ c'.hom) : c = c' := by
  obtain ⟨s, t, p, q, φ⟩ := c
  obtain ⟨s', t', p', q', φ'⟩ := c'
  dsimp only at hsrc htgt hdom hcod hhom
  subst hsrc htgt
  obtain rfl := eq_of_heq hdom
  obtain rfl := eq_of_heq hcod
  obtain rfl := eq_of_heq hhom
  rfl

theorem pathCell_id_ext {a b a' b' : B} {P : Quiver.Path a b} {P' : Quiver.Path a' b'}
    (ha : a = a') (hb : b = b') (h : P ≍ P') :
    (⟨a, b, P, P, 𝟙 _⟩ : PathCell B) = ⟨a', b', P', P', 𝟙 _⟩ := by
  subst ha hb
  obtain rfl := eq_of_heq h
  rfl

theorem pathCell_hom_eq {a b : B} {P Q : Quiver.Path a b}
    {φ ψ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q}
    (h : (⟨a, b, P, Q, φ⟩ : PathCell B) = ⟨a, b, P, Q, ψ⟩) : φ = ψ := by
  obtain ⟨-, -, -, -, hh⟩ := PathCell.mk.inj h
  exact eq_of_heq hh

theorem pathCell_eqToHom {a b : B} {P P' Q Q' : Quiver.Path a b} (hP : P = P') (hQ : Q' = Q)
    (φ : pathComp (𝟭q B) P' ⟶ pathComp (𝟭q B) Q') :
    (⟨a, b, P, Q, eqToHom (congrArg (pathComp (𝟭q B)) hP) ≫ φ ≫
        eqToHom (congrArg (pathComp (𝟭q B)) hQ)⟩ : PathCell B) = ⟨a, b, P', Q', φ⟩ := by
  subst hP hQ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem eqToHom_eq_pathCompCompIso_assoc {a b c d : B} (p : Quiver.Path a b)
    (q : Quiver.Path b c) (r : Quiver.Path c d) {pq : Quiver.Path a c} {qr : Quiver.Path b d}
    {pqr pqr' : Quiver.Path a d} (h₁ : pq = p.comp q) (h₂ : qr = q.comp r) (h₃ : pqr = pq.comp r)
    (h₄ : pqr' = p.comp qr) (h : pqr = pqr') :
    eqToHom (congrArg (pathComp (𝟭q B)) h) =
      (eqToHom (congrArg (pathComp (𝟭q B)) h₃) ≫ (pathCompCompIso (𝟭q B) pq r).hom) ≫
        (eqToHom (congrArg (pathComp (𝟭q B)) h₁) ≫ (pathCompCompIso (𝟭q B) p q).hom) ▷
          pathComp (𝟭q B) r ≫ (α_ _ _ _).hom ≫
        pathComp (𝟭q B) p ◁ ((pathCompCompIso (𝟭q B) q r).inv ≫
          eqToHom (congrArg (pathComp (𝟭q B)) h₂.symm)) ≫
        ((pathCompCompIso (𝟭q B) p qr).inv ≫ eqToHom (congrArg (pathComp (𝟭q B)) h₄.symm)) := by
  subst h₁ h₂ h₃ h₄
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [Bicategory.pathCompCompIso_assoc_assoc]
  simp

theorem pathCell_comp_eqToHom {a b : B} {P Q Q' : Quiver.Path a b} (hQ : Q = Q')
    (φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q) :
    (⟨a, b, P, Q, φ⟩ : PathCell B) =
      ⟨a, b, P, Q', φ ≫ eqToHom (congrArg (pathComp (𝟭q B)) hQ)⟩ := by
  subst hQ
  simp only [eqToHom_refl, Category.comp_id]

theorem pathCell_eqToHom_comp {a b : B} {P P' Q : Quiver.Path a b} (hP : P = P')
    (φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q) :
    (⟨a, b, P, Q, φ⟩ : PathCell B) =
      ⟨a, b, P', Q, eqToHom (congrArg (pathComp (𝟭q B)) hP.symm) ≫ φ⟩ := by
  subst hP
  simp only [eqToHom_refl, Category.id_comp]

theorem pathCell_whisker_eq {y z y' z' : B} {W : Quiver.Path y y} {W' : Quiver.Path y' y'}
    {P Q : Quiver.Path y z} {P' Q' : Quiver.Path y' z'}
    {φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q} {φ' : pathComp (𝟭q B) P' ⟶ pathComp (𝟭q B) Q'}
    (hW : W ≍ W') (h : (⟨y, z, P, Q, φ⟩ : PathCell B) = ⟨y', z', P', Q', φ'⟩) :
    (⟨y, z, W.comp P, W.comp Q, (pathCompCompIso (𝟭q B) W P).hom ≫ pathComp (𝟭q B) W ◁ φ ≫
        (pathCompCompIso (𝟭q B) W Q).inv⟩ : PathCell B) =
      ⟨y', z', W'.comp P', W'.comp Q', (pathCompCompIso (𝟭q B) W' P').hom ≫
        pathComp (𝟭q B) W' ◁ φ' ≫ (pathCompCompIso (𝟭q B) W' Q').inv⟩ := by
  obtain ⟨hy, hz, hP, hQ, hφ⟩ := PathCell.mk.inj h
  subst hy hz
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hQ
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hW
  rfl

theorem pathComp_mapPath_comp (F : Prefunctor V W) (G : Prefunctor W B) {x y : V} :
    ∀ p : Path x y, pathComp G (F.mapPath p) = pathComp (F ⋙q G) p
  | .nil => rfl
  | .cons p e => congrArg (· ≫ G.map (F.map e)) (pathComp_mapPath_comp F G p)

theorem pathComp_mapPath (F : Prefunctor V B) {x y : V} (p : Path x y) :
    pathComp (𝟭q B) (F.mapPath p) = pathComp F p :=
  pathComp_mapPath_comp F (𝟭q B) p

theorem whiskerRight_heq {a b c : B} {f g f' g' : a ⟶ b} {h h' : b ⟶ c} (hf : f = f')
    (hg : g = g') (hh : h = h') {η : f ⟶ g} {η' : f' ⟶ g'} (hη : η ≍ η') : η ▷ h ≍ η' ▷ h' := by
  subst hf hg hh
  obtain rfl := eq_of_heq hη
  rfl

theorem whiskerLeft_heq {a b c : B} {f f' : a ⟶ b} {g h g' h' : b ⟶ c} (hf : f = f')
    (hg : g = g') (hh : h = h') {η : g ⟶ h} {η' : g' ⟶ h'} (hη : η ≍ η') : f ◁ η ≍ f' ◁ η' := by
  subst hf hg hh
  obtain rfl := eq_of_heq hη
  rfl

theorem heq_of_id_whiskerLeft_heq {a b : B} {f g f' g' : a ⟶ b} {η : f ⟶ g} {η' : f' ⟶ g'}
    (hf : f = f') (hg : g = g') (h : 𝟙 a ◁ η ≍ 𝟙 a ◁ η') : η ≍ η' := by
  subst hf hg
  refine heq_of_eq ?_
  simpa using congrArg (fun t => (λ_ f).inv ≫ t ≫ (λ_ g).hom) (eq_of_heq h)

end PathCell

end Bicategory

end CategoryTheory

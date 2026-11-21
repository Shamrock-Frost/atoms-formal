import Atoms.ForMathlib.CategoryTheory.Bicategory.Structural
import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary

namespace CategoryTheory.Bicategory

open Quiver (Path)

universe w v u w₂ v₂ u₂ w₃ v₃ u₃ v₁ u₁

variable {V : Type u₁} [Quiver.{v₁} V] {B : Type u} [Bicategory.{w, v} B] {C : Type u₂}
  [Bicategory.{w₂, v₂} C]

section Comparison

variable (F : B ⥤ᵖ C) {a b c : B}

private theorem conj_comp {D : Type*} [Category D] {X X' Y Y' Z Z' : D} (α : X ≅ X') (β : Y ≅ Y')
    (γ : Z ≅ Z') (f : X ⟶ Y) (g : Y ⟶ Z) :
    (α.inv ≫ f ≫ β.hom) ≫ β.inv ≫ g ≫ γ.hom = α.inv ≫ (f ≫ g) ≫ γ.hom := by
  simp

private theorem map₂_rightUnitor_inv_comp {f : a ⟶ b} {f' : F.obj a ⟶ F.obj b}
    (θ : F.map f ≅ f') :
    F.map₂ (ρ_ f).inv ≫ (F.mapComp f (𝟙 b)).hom ≫ (θ.hom ▷ F.map (𝟙 b) ≫ f' ◁ (F.mapId b).hom) =
      θ.hom ≫ (ρ_ f').inv := by
  have h : F.map₂ (ρ_ f).inv ≫ (F.mapComp f (𝟙 b)).hom = (ρ_ _).inv ≫ _ ◁ (F.mapId _).inv := by
    rw [Pseudofunctor.mapComp_id_right_hom, ← F.map₂_comp_assoc, Iso.inv_hom_id, F.map₂_id,
      Category.id_comp]
  rw [reassoc_of% h, whisker_exchange_assoc, ← whiskerLeft_comp, Iso.inv_hom_id,
    whiskerLeft_id, Category.comp_id, rightUnitor_inv_naturality]

private theorem map₂_whiskerRight_associator_comp {d : B} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    (h : c ⟶ d) {f' : F.obj a ⟶ F.obj b} {g' : F.obj b ⟶ F.obj c} {k' : F.obj a ⟶ F.obj c}
    (θf : F.map f ≅ f') (θg : F.map g ≅ g') (θk : F.map k ≅ k') (κ : k ⟶ f ≫ g)
    (κ' : k' ⟶ f' ≫ g')
    (H : F.map₂ κ ≫ (F.mapComp f g).hom ≫ (θf.hom ▷ F.map g ≫ f' ◁ θg.hom) = θk.hom ≫ κ') :
    F.map₂ (κ ▷ h ≫ (α_ f g h).hom) ≫ (F.mapComp f (g ≫ h)).hom ≫
        (θf.hom ▷ F.map (g ≫ h) ≫ f' ◁ ((F.mapComp g h).hom ≫ θg.hom ▷ F.map h)) =
      ((F.mapComp k h).hom ≫ θk.hom ▷ F.map h) ≫ κ' ▷ F.map h ≫ (α_ f' g' (F.map h)).hom := by
  have ih := congrArg (· ▷ F.map h) H
  simp only [comp_whiskerRight] at ih
  simp only [F.map₂_comp, F.map₂_whisker_right, F.map₂_associator, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [whisker_exchange_assoc, ← whiskerLeft_comp, Iso.inv_hom_id_assoc,
    ← associator_naturality_left_assoc, ← associator_naturality_middle, reassoc_of% ih]

private theorem conj_map₂_whiskerLeft {f : a ⟶ b} {g h : b ⟶ c} {k k' : a ⟶ c} (η : g ⟶ h)
    {f' : F.obj a ⟶ F.obj b} {g' h' : F.obj b ⟶ F.obj c} {k₁ k₁' : F.obj a ⟶ F.obj c}
    (θf : F.map f ≅ f') (θg : F.map g ≅ g') (θh : F.map h ≅ h') (θk : F.map k ≅ k₁)
    (θk' : F.map k' ≅ k₁') (κ : k ≅ f ≫ g) (κh : k' ≅ f ≫ h) (κ' : k₁ ≅ f' ≫ g')
    (κh' : k₁' ≅ f' ≫ h')
    (H : F.map₂ κ.hom ≫ (F.mapComp f g).hom ≫ (θf.hom ▷ F.map g ≫ f' ◁ θg.hom) =
      θk.hom ≫ κ'.hom)
    (H' : F.map₂ κh.hom ≫ (F.mapComp f h).hom ≫ (θf.hom ▷ F.map h ≫ f' ◁ θh.hom) =
      θk'.hom ≫ κh'.hom) :
    θk.inv ≫ F.map₂ (κ.hom ≫ f ◁ η ≫ κh.inv) ≫ θk'.hom =
      κ'.hom ≫ f' ◁ (θg.inv ≫ F.map₂ η ≫ θh.hom) ≫ κh'.inv := by
  have e : θk.inv ≫ F.map₂ κ.hom =
      κ'.hom ≫ (f' ◁ θg.inv ≫ θf.inv ▷ F.map g) ≫ (F.mapComp f g).inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% H]
    simp [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]
  have e' : F.map₂ κh.inv ≫ θk'.hom =
      (F.mapComp f h).hom ≫ (θf.hom ▷ F.map h ≫ f' ◁ θh.hom) ≫ κh'.inv := by
    rw [← cancel_mono κh'.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← H', ← F.map₂_comp_assoc, Iso.inv_hom_id, F.map₂_id, Category.id_comp]
  simp only [F.map₂_comp, Category.assoc]
  rw [reassoc_of% e, e', F.map₂_whisker_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc, ← whisker_exchange_assoc,
    inv_hom_whiskerRight_assoc]

private theorem conj_map₂_whiskerRight {f g : a ⟶ b} {h : b ⟶ c} {k k' : a ⟶ c} (η : f ⟶ g)
    {f' g' : F.obj a ⟶ F.obj b} {h' : F.obj b ⟶ F.obj c} {k₁ k₁' : F.obj a ⟶ F.obj c}
    (θf : F.map f ≅ f') (θg : F.map g ≅ g') (θh : F.map h ≅ h') (θk : F.map k ≅ k₁)
    (θk' : F.map k' ≅ k₁') (κ : k ≅ f ≫ h) (κg : k' ≅ g ≫ h) (κ' : k₁ ≅ f' ≫ h')
    (κg' : k₁' ≅ g' ≫ h')
    (H : F.map₂ κ.hom ≫ (F.mapComp f h).hom ≫ (θf.hom ▷ F.map h ≫ f' ◁ θh.hom) =
      θk.hom ≫ κ'.hom)
    (H' : F.map₂ κg.hom ≫ (F.mapComp g h).hom ≫ (θg.hom ▷ F.map h ≫ g' ◁ θh.hom) =
      θk'.hom ≫ κg'.hom) :
    θk.inv ≫ F.map₂ (κ.hom ≫ η ▷ h ≫ κg.inv) ≫ θk'.hom =
      κ'.hom ≫ (θf.inv ≫ F.map₂ η ≫ θg.hom) ▷ h' ≫ κg'.inv := by
  have e : θk.inv ≫ F.map₂ κ.hom =
      κ'.hom ≫ (f' ◁ θh.inv ≫ θf.inv ▷ F.map h) ≫ (F.mapComp f h).inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% H]
    simp [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]
  have e' : F.map₂ κg.inv ≫ θk'.hom =
      (F.mapComp g h).hom ≫ (θg.hom ▷ F.map h ≫ g' ◁ θh.hom) ≫ κg'.inv := by
    rw [← cancel_mono κg'.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← H', ← F.map₂_comp_assoc, Iso.inv_hom_id, F.map₂_id, Category.id_comp]
  simp only [F.map₂_comp, Category.assoc]
  rw [reassoc_of% e, e', F.map₂_whisker_right]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, comp_whiskerRight]
  rw [whisker_exchange_assoc, whisker_exchange_assoc, whisker_exchange_assoc,
    whiskerLeft_inv_hom_assoc]

private theorem mapComp_hom_whiskerRight_eqToHom {f f₀ : a ⟶ b} (e : b ⟶ c)
    {f' f₀' : F.obj a ⟶ F.obj b} (hf : f₀ = f) (hf' : f' = f₀') (θ : F.map f ≅ f')
    (θ₀ : F.map f₀ ≅ f₀') (H : θ₀.hom = F.map₂ (eqToHom hf) ≫ θ.hom ≫ eqToHom hf') :
    (F.mapComp f₀ e).hom ≫ θ₀.hom ▷ F.map e =
      F.map₂ (eqToHom (congrArg (· ≫ e) hf)) ≫ ((F.mapComp f e).hom ≫ θ.hom ▷ F.map e) ≫
        eqToHom (congrArg (· ≫ F.map e) hf') := by
  subst hf hf'
  obtain rfl : θ₀ = θ := Iso.ext (by simpa using H)
  simp

private theorem conj_map₂_eqToHom {f f₀ g g₀ : a ⟶ b} {f' f₀' g' g₀' : F.obj a ⟶ F.obj b}
    (hf : f₀ = f) (hf' : f' = f₀') (hg : g₀ = g) (hg' : g' = g₀') (θf : F.map f ≅ f')
    (θf₀ : F.map f₀ ≅ f₀') (θg : F.map g ≅ g') (θg₀ : F.map g₀ ≅ g₀')
    (Hf : θf₀.hom = F.map₂ (eqToHom hf) ≫ θf.hom ≫ eqToHom hf')
    (Hg : θg₀.hom = F.map₂ (eqToHom hg) ≫ θg.hom ≫ eqToHom hg') (η : f ⟶ g) :
    θf₀.inv ≫ F.map₂ (eqToHom hf ≫ η ≫ eqToHom hg.symm) ≫ θg₀.hom =
      eqToHom hf'.symm ≫ (θf.inv ≫ F.map₂ η ≫ θg.hom) ≫ eqToHom hg' := by
  subst hf hf' hg hg'
  obtain rfl : θf₀ = θf := Iso.ext (by simpa using Hf)
  obtain rfl : θg₀ = θg := Iso.ext (by simpa using Hg)
  simp

private theorem comp_mapComp_hom_whiskerRight {D : Type u₃} [Bicategory.{w₃, v₃} D] (H : C ⥤ᵖ D)
    {f : a ⟶ b} (e : b ⟶ c) {f₁ : F.obj a ⟶ F.obj b} {f₂ : H.obj (F.obj a) ⟶ H.obj (F.obj b)}
    (θ₁ : F.map f ≅ f₁) (θ₂ : H.map f₁ ≅ f₂) (θ : H.map (F.map f) ≅ f₂)
    (h : θ.hom = H.map₂ θ₁.hom ≫ θ₂.hom) :
    (H.map₂ (F.mapComp f e).hom ≫ (H.mapComp (F.map f) (F.map e)).hom) ≫ θ.hom ▷ H.map (F.map e) =
      H.map₂ ((F.mapComp f e).hom ≫ θ₁.hom ▷ F.map e) ≫ (H.mapComp f₁ (F.map e)).hom ≫
        θ₂.hom ▷ H.map (F.map e) := by
  rw [h, H.map₂_comp, H.map₂_whisker_right, comp_whiskerRight]
  simp

private theorem conj_comp_map₂ {D : Type u₃} [Bicategory.{w₃, v₃} D] (H : C ⥤ᵖ D)
    {f g : a ⟶ b} {f₁ g₁ : F.obj a ⟶ F.obj b} {f₂ g₂ : H.obj (F.obj a) ⟶ H.obj (F.obj b)}
    (θf : F.map f ≅ f₁) (θg : F.map g ≅ g₁) (θf' : H.map f₁ ≅ f₂) (θg' : H.map g₁ ≅ g₂)
    (θf₂ : H.map (F.map f) ≅ f₂) (θg₂ : H.map (F.map g) ≅ g₂)
    (hf : θf₂.hom = H.map₂ θf.hom ≫ θf'.hom) (hg : θg₂.hom = H.map₂ θg.hom ≫ θg'.hom)
    (η : f ⟶ g) :
    θf₂.inv ≫ H.map₂ (F.map₂ η) ≫ θg₂.hom =
      θf'.inv ≫ H.map₂ (θf.inv ≫ F.map₂ η ≫ θg.hom) ≫ θg'.hom := by
  rw [Iso.inv_comp_eq, hf, hg]
  simp only [H.map₂_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← H.map₂_comp_assoc θf.hom, Iso.hom_inv_id, H.map₂_id, Category.id_comp]

end Comparison

section PathCompMap

variable (G : Prefunctor V B) (F : B ⥤ᵖ C)

def pathCompMapIso {x : V} : ∀ {y : V} (p : Path x y),
    F.map (pathComp G p) ≅ pathComp (G ⋙q F.toPrefunctor) p
  | _, .nil => F.mapId (G.obj x)
  | _, .cons p e => F.mapComp (pathComp G p) (G.map e) ≪≫
      whiskerRightIso (pathCompMapIso p) (F.map (G.map e))

@[reassoc]
theorem pathCompMapIso_comp {x y : V} (p : Path x y) : ∀ {z : V} (q : Path y z),
    F.map₂ (pathCompCompIso G p q).hom ≫ (F.mapComp _ _).hom ≫
        ((pathCompMapIso G F p).hom ▷ _ ≫ _ ◁ (pathCompMapIso G F q).hom) =
      (pathCompMapIso G F (p.comp q)).hom ≫ (pathCompCompIso (G ⋙q F.toPrefunctor) p q).hom
  | _, .nil => by
    rw [pathCompCompIso_comp_nil, pathCompCompIso_comp_nil]
    exact map₂_rightUnitor_inv_comp F (pathCompMapIso G F p)
  | _, .cons q e => by
    rw [pathCompCompIso_cons_hom, pathCompCompIso_cons_hom]
    exact map₂_whiskerRight_associator_comp F (G.map e) (pathCompMapIso G F p)
      (pathCompMapIso G F q) (pathCompMapIso G F (p.comp q)) _ _ (pathCompMapIso_comp p q)

def pathCompMap₂ {x y : V} {p q : Path x y} (η : pathComp G p ⟶ pathComp G q) :
    pathComp (G ⋙q F.toPrefunctor) p ⟶ pathComp (G ⋙q F.toPrefunctor) q :=
  (pathCompMapIso G F p).inv ≫ F.map₂ η ≫ (pathCompMapIso G F q).hom

theorem pathCompMap₂_id {x y : V} (p : Path x y) :
    pathCompMap₂ G F (𝟙 (pathComp G p)) = 𝟙 _ :=
  (congrArg (fun t => (pathCompMapIso G F p).inv ≫ t ≫ (pathCompMapIso G F p).hom)
    (F.map₂_id _)).trans ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (Iso.inv_hom_id _))

@[reassoc]
theorem pathCompMap₂_comp {x y : V} {p q r : Path x y} (η : pathComp G p ⟶ pathComp G q)
    (θ : pathComp G q ⟶ pathComp G r) :
    pathCompMap₂ G F (η ≫ θ) = pathCompMap₂ G F η ≫ pathCompMap₂ G F θ :=
  (congrArg (fun t => (pathCompMapIso G F p).inv ≫ t ≫ (pathCompMapIso G F r).hom)
    (F.map₂_comp η θ)).trans (conj_comp _ _ _ _ _).symm

theorem pathCompMap₂_eqToHom_comp_eqToHom {x y : V} {p p' q q' : Path x y} (hp : p = p')
    (hq : q' = q) (η : pathComp G p' ⟶ pathComp G q') :
    pathCompMap₂ G F (eqToHom (congrArg (pathComp G) hp) ≫ η ≫
        eqToHom (congrArg (pathComp G) hq)) =
      eqToHom (congrArg (pathComp (G ⋙q F.toPrefunctor)) hp) ≫ pathCompMap₂ G F η ≫
        eqToHom (congrArg (pathComp (G ⋙q F.toPrefunctor)) hq) := by
  subst hp hq
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem pathCompMap₂_whiskerLeft {x y z : V} (p : Path x y) {q q' : Path y z}
    (η : pathComp G q ⟶ pathComp G q') :
    pathCompMap₂ G F ((pathCompCompIso G p q).hom ≫ pathComp G p ◁ η ≫
        (pathCompCompIso G p q').inv) =
      (pathCompCompIso (G ⋙q F.toPrefunctor) p q).hom ≫
        pathComp (G ⋙q F.toPrefunctor) p ◁ pathCompMap₂ G F η ≫
          (pathCompCompIso (G ⋙q F.toPrefunctor) p q').inv :=
  conj_map₂_whiskerLeft F η (pathCompMapIso G F p) (pathCompMapIso G F q)
    (pathCompMapIso G F q') (pathCompMapIso G F (p.comp q)) (pathCompMapIso G F (p.comp q'))
    (pathCompCompIso G p q) (pathCompCompIso G p q') (pathCompCompIso (G ⋙q F.toPrefunctor) p q)
    (pathCompCompIso (G ⋙q F.toPrefunctor) p q') (pathCompMapIso_comp G F p q)
    (pathCompMapIso_comp G F p q')

theorem pathCompMap₂_whiskerRight {x y z : V} {p p' : Path x y}
    (η : pathComp G p ⟶ pathComp G p') (q : Path y z) :
    pathCompMap₂ G F ((pathCompCompIso G p q).hom ≫ η ▷ pathComp G q ≫
        (pathCompCompIso G p' q).inv) =
      (pathCompCompIso (G ⋙q F.toPrefunctor) p q).hom ≫
        pathCompMap₂ G F η ▷ pathComp (G ⋙q F.toPrefunctor) q ≫
          (pathCompCompIso (G ⋙q F.toPrefunctor) p' q).inv :=
  conj_map₂_whiskerRight F η (pathCompMapIso G F p) (pathCompMapIso G F p')
    (pathCompMapIso G F q) (pathCompMapIso G F (p.comp q)) (pathCompMapIso G F (p'.comp q))
    (pathCompCompIso G p q) (pathCompCompIso G p' q) (pathCompCompIso (G ⋙q F.toPrefunctor) p q)
    (pathCompCompIso (G ⋙q F.toPrefunctor) p' q) (pathCompMapIso_comp G F p q)
    (pathCompMapIso_comp G F p' q)

theorem pathCompMap₂_pathWhisker {x y z w : V} (p : Path x y) {q q' : Path y z}
    (η : pathComp G q ⟶ pathComp G q') (r : Path z w) :
    pathCompMap₂ G F (pathWhisker G p η r) =
      pathWhisker (G ⋙q F.toPrefunctor) p (pathCompMap₂ G F η) r :=
  (pathCompMap₂_whiskerLeft G F p _).trans
    (congrArg (fun t => (pathCompCompIso (G ⋙q F.toPrefunctor) p (q.comp r)).hom ≫
      pathComp (G ⋙q F.toPrefunctor) p ◁ t ≫
        (pathCompCompIso (G ⋙q F.toPrefunctor) p (q'.comp r)).inv)
      (pathCompMap₂_whiskerRight G F η r))

theorem pathCompMapIso_idPseudofunctor {x : V} : ∀ {y : V} (p : Path x y),
    (pathCompMapIso G (Pseudofunctor.id B) p).hom = 𝟙 (pathComp G p)
  | _, .nil => rfl
  | _, .cons p e => (Category.id_comp _).trans
    ((congrArg (· ▷ G.map e) (pathCompMapIso_idPseudofunctor p)).trans (id_whiskerRight _ _))

theorem pathCompMap₂_idPseudofunctor {x y : V} {p q : Path x y}
    (η : pathComp G p ⟶ pathComp G q) : pathCompMap₂ G (Pseudofunctor.id B) η = η := by
  have h (p : Path x y) : pathCompMapIso G (Pseudofunctor.id B) p = Iso.refl (pathComp G p) :=
    Iso.ext (pathCompMapIso_idPseudofunctor G p)
  exact (congrArg₂ (fun α β : pathComp G _ ≅ pathComp G _ => α.inv ≫ η ≫ β.hom) (h p) (h q)).trans
    ((Category.id_comp _).trans (Category.comp_id _))

theorem pathCompMapIso_mapPath {x : V} : ∀ {y : V} (p : Path x y),
    (pathCompMapIso (𝟭q B) F (G.mapPath p)).hom =
      F.map₂ (eqToHom (pathComp_mapPath G p)) ≫ (pathCompMapIso G F p).hom ≫
        eqToHom (pathComp_mapPath_comp G F.toPrefunctor p).symm
  | _, .nil => ((congrArg₂ (· ≫ ·) (F.map₂_id _) (Category.comp_id _)).trans
    (Category.id_comp _)).symm
  | _, .cons p e => mapComp_hom_whiskerRight_eqToHom F (G.map e) (pathComp_mapPath G p)
    (pathComp_mapPath_comp G F.toPrefunctor p).symm (pathCompMapIso G F p)
    (pathCompMapIso (𝟭q B) F (G.mapPath p)) (pathCompMapIso_mapPath p)

def PathCell.map (c : PathCell B) (F : B ⥤ᵖ C) : PathCell C :=
  PathCell.ofHom F.toPrefunctor c.dom c.cod (pathCompMap₂ (𝟭q B) F c.hom)

theorem PathCell.map_ofHom {x y : V} (p q : Path x y) (η : pathComp G p ⟶ pathComp G q) :
    (PathCell.ofHom G p q η).map F =
      PathCell.ofHom (G ⋙q F.toPrefunctor) p q (pathCompMap₂ G F η) := by
  have key : pathCompMap₂ (𝟭q B) F (eqToHom (pathComp_mapPath G p) ≫ η ≫
      eqToHom (pathComp_mapPath G q).symm) =
      eqToHom (pathComp_mapPath_comp G F.toPrefunctor p) ≫ pathCompMap₂ G F η ≫
        eqToHom (pathComp_mapPath_comp G F.toPrefunctor q).symm :=
    conj_map₂_eqToHom F (pathComp_mapPath G p) (pathComp_mapPath_comp G F.toPrefunctor p).symm
      (pathComp_mapPath G q) (pathComp_mapPath_comp G F.toPrefunctor q).symm
      (pathCompMapIso G F p) (pathCompMapIso (𝟭q B) F (G.mapPath p)) (pathCompMapIso G F q)
      (pathCompMapIso (𝟭q B) F (G.mapPath q)) (pathCompMapIso_mapPath G F p)
      (pathCompMapIso_mapPath G F q) η
  refine PathCell.ext rfl rfl (heq_of_eq (Prefunctor.mapPath_comp_apply _ _ _).symm)
    (heq_of_eq (Prefunctor.mapPath_comp_apply _ _ _).symm) ?_
  refine ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans ((heq_of_eq key).trans ?_)
  exact ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans
    ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm

variable {D : Type u₃} [Bicategory.{w₃, v₃} D] (H : C ⥤ᵖ D)

theorem pathCompMapIso_compPseudofunctor {x : V} : ∀ {y : V} (p : Path x y),
    (pathCompMapIso G (F.comp H) p).hom =
      H.map₂ (pathCompMapIso G F p).hom ≫ (pathCompMapIso (G ⋙q F.toPrefunctor) H p).hom
  | _, .nil => rfl
  | _, .cons p e => comp_mapComp_hom_whiskerRight F H (G.map e) (pathCompMapIso G F p)
    (pathCompMapIso (G ⋙q F.toPrefunctor) H p) (pathCompMapIso G (F.comp H) p)
    (pathCompMapIso_compPseudofunctor p)

theorem pathCompMap₂_compPseudofunctor {x y : V} {p q : Path x y}
    (η : pathComp G p ⟶ pathComp G q) :
    pathCompMap₂ G (F.comp H) η =
      pathCompMap₂ (G ⋙q F.toPrefunctor) H (pathCompMap₂ G F η) :=
  conj_comp_map₂ F H (pathCompMapIso G F p) (pathCompMapIso G F q)
    (pathCompMapIso (G ⋙q F.toPrefunctor) H p) (pathCompMapIso (G ⋙q F.toPrefunctor) H q)
    (pathCompMapIso G (F.comp H) p) (pathCompMapIso G (F.comp H) q)
    (pathCompMapIso_compPseudofunctor G F H p) (pathCompMapIso_compPseudofunctor G F H q) η

end PathCompMap

section Lift

section Comparison

variable (F : B ⥤ᵖ C) {a b c : B}

private def compIso {f : a ⟶ b} {g : b ⟶ c} {f' : F.obj a ⟶ F.obj b} {g' : F.obj b ⟶ F.obj c}
    (θf : F.map f ≅ f') (θg : F.map g ≅ g') : F.map (f ≫ g) ≅ f' ≫ g' :=
  F.mapComp f g ≪≫ (whiskerRightIso θf (F.map g) ≪≫ whiskerLeftIso f' θg)

private theorem map₂_whiskerLeft_eq (f : a ⟶ b) {g h : b ⟶ c} {η : g ⟶ h}
    {f' : F.obj a ⟶ F.obj b} {g' h' : F.obj b ⟶ F.obj c} (θf : F.map f ≅ f')
    {θg : F.map g ≅ g'} {θh : F.map h ≅ h'} {η' : g' ⟶ h'}
    (H : F.map₂ η = θg.hom ≫ η' ≫ θh.inv) :
    F.map₂ (f ◁ η) = (compIso F θf θg).hom ≫ f' ◁ η' ≫ (compIso F θf θh).inv := by
  rw [F.map₂_whisker_left, H]
  simp [compIso, ← whisker_exchange_assoc]

private theorem map₂_whiskerRight_eq {f g : a ⟶ b} (h : b ⟶ c) {η : f ⟶ g}
    {f' g' : F.obj a ⟶ F.obj b} {h' : F.obj b ⟶ F.obj c} {θf : F.map f ≅ f'}
    {θg : F.map g ≅ g'} (θh : F.map h ≅ h') {η' : f' ⟶ g'}
    (H : F.map₂ η = θf.hom ≫ η' ≫ θg.inv) :
    F.map₂ (η ▷ h) = (compIso F θf θh).hom ≫ η' ▷ h' ≫ (compIso F θg θh).inv := by
  rw [F.map₂_whisker_right, H]
  simp [compIso, whisker_exchange_assoc]

private theorem map₂Iso_associator {d : B} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    {f' : F.obj a ⟶ F.obj b} {g' : F.obj b ⟶ F.obj c} {h' : F.obj c ⟶ F.obj d}
    (θf : F.map f ≅ f') (θg : F.map g ≅ g') (θh : F.map h ≅ h') :
    F.map₂Iso (α_ f g h) = compIso F (compIso F θf θg) θh ≪≫ α_ f' g' h' ≪≫
      (compIso F θf (compIso F θg θh)).symm := by
  ext
  simp only [Functor.mapIso_hom, PrelaxFunctor.mapFunctor_map, F.map₂_associator, compIso,
    Iso.trans_symm, Iso.trans_assoc, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
    comp_whiskerRight, whisker_assoc, comp_whiskerLeft, Iso.symm_hom, whiskerLeftIso_inv,
    Iso.trans_inv, whiskerRightIso_inv, Category.assoc, whiskerLeft_comp, Iso.inv_hom_id_assoc,
    whiskerLeft_whiskerLeft_hom_inv_assoc, whiskerLeft_hom_inv_whiskerRight_assoc,
    Iso.cancel_iso_hom_left]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, hom_inv_whiskerRight_assoc]

private theorem map₂Iso_rightUnitor {f : a ⟶ b} {f' : F.obj a ⟶ F.obj b} (θf : F.map f ≅ f') :
    F.map₂Iso (ρ_ f) = compIso F θf (F.mapId b) ≪≫ ρ_ f' ≪≫ θf.symm := by
  ext
  simp [compIso, F.map₂_right_unitor, ← whisker_exchange_assoc]

private theorem map₂Iso_leftUnitor {f : a ⟶ b} {f' : F.obj a ⟶ F.obj b} (θf : F.map f ≅ f') :
    F.map₂Iso (λ_ f) = compIso F (F.mapId a) θf ≪≫ λ_ f' ≪≫ θf.symm := by
  ext
  simp [compIso, F.map₂_left_unitor]

end Comparison

open FreeBicategory

variable (G : Prefunctor V B) (F : B ⥤ᵖ C)

def liftMapIso : ∀ {a b : FreeBicategory V} (f : a ⟶ b),
    F.map ((lift G).map f) ≅ (lift (G ⋙q F.toPrefunctor)).map f
  | _, _, .of e => Iso.refl (F.map (G.map e))
  | _, _, .id a => F.mapId (G.obj a)
  | _, _, .comp f g => F.mapComp ((lift G).map f) ((lift G).map g) ≪≫
      (whiskerRightIso (liftMapIso f) (F.map ((lift G).map g)) ≪≫
        whiskerLeftIso ((lift (G ⋙q F.toPrefunctor)).map f) (liftMapIso g))

private theorem map₂_liftHom₂ : ∀ {a b : FreeBicategory V} {f g : a ⟶ b} (η : Hom₂ f g),
    F.map₂ (liftHom₂ G η) = (liftMapIso G F f).hom ≫ liftHom₂ (G ⋙q F.toPrefunctor) η ≫
      (liftMapIso G F g).inv
  | _, _, _, _, .id f => (F.map₂_id _).trans
    (((congrArg (_ ≫ ·) (Category.id_comp _)).trans (Iso.hom_inv_id _)).symm)
  | _, _, _, _, .vcomp η θ => (F.map₂_comp _ _).trans
    ((congrArg₂ (· ≫ ·) (map₂_liftHom₂ η) (map₂_liftHom₂ θ)).trans
      (conj_comp (liftMapIso G F _).symm (liftMapIso G F _).symm (liftMapIso G F _).symm _ _))
  | _, _, _, _, .whisker_left f η => map₂_whiskerLeft_eq F _ (liftMapIso G F f) (map₂_liftHom₂ η)
  | _, _, _, _, .whisker_right h η => map₂_whiskerRight_eq F _ (liftMapIso G F h) (map₂_liftHom₂ η)
  | _, _, _, _, .associator f g h => congrArg Iso.hom
    (map₂Iso_associator F (liftMapIso G F f) (liftMapIso G F g) (liftMapIso G F h))
  | _, _, _, _, .associator_inv f g h => (congrArg Iso.inv
    (map₂Iso_associator F (liftMapIso G F f) (liftMapIso G F g) (liftMapIso G F h))).trans
      (Category.assoc _ _ _)
  | _, _, _, _, .right_unitor f => congrArg Iso.hom (map₂Iso_rightUnitor F (liftMapIso G F f))
  | _, _, _, _, .right_unitor_inv f => (congrArg Iso.inv
    (map₂Iso_rightUnitor F (liftMapIso G F f))).trans (Category.assoc _ _ _)
  | _, _, _, _, .left_unitor f => congrArg Iso.hom (map₂Iso_leftUnitor F (liftMapIso G F f))
  | _, _, _, _, .left_unitor_inv f => (congrArg Iso.inv
    (map₂Iso_leftUnitor F (liftMapIso G F f))).trans (Category.assoc _ _ _)

@[reassoc]
theorem map₂_lift_map₂ {a b : FreeBicategory V} {f g : a ⟶ b} (η : f ⟶ g) :
    F.map₂ ((lift G).map₂ η) =
      (liftMapIso G F f).hom ≫ (lift (G ⋙q F.toPrefunctor)).map₂ η ≫ (liftMapIso G F g).inv :=
  Quot.inductionOn η (map₂_liftHom₂ G F)

end Lift

section StrictlyUnitary

open FreeBicategory

section Comparison

variable (F : B ⥤ᵖ C) {a b c : B}

private theorem mapComp_trans_whiskerRightIso_trans_refl {f : a ⟶ b} (g : b ⟶ c)
    {f' : F.obj a ⟶ F.obj b} {θ θ' : F.map f ≅ f'} (h : θ = θ') :
    F.mapComp f g ≪≫ (whiskerRightIso θ (F.map g) ≪≫ whiskerLeftIso f' (Iso.refl (F.map g))) =
      F.mapComp f g ≪≫ whiskerRightIso θ' (F.map g) := by
  subst h
  ext
  simp

private theorem mapComp_hom_whiskerRight_eqToHom_eqToIso {f f₀ : a ⟶ b} (e : b ⟶ c)
    {f' f₀' : F.obj a ⟶ F.obj b} {e' : F.obj b ⟶ F.obj c} (hf : f₀ = f) (hf' : f' = f₀')
    (θe : F.map e ≅ e') (he : F.map e = e') (hθe : θe = eqToIso he) (θ : F.map f ≅ f')
    (θ₀ : F.map f₀ ≅ f₀') (H : θ₀.hom = F.map₂ (eqToHom hf) ≫ θ.hom ≫ eqToHom hf') :
    (F.mapComp f₀ e).hom ≫ θ₀.hom ▷ F.map e =
      F.map₂ (eqToHom (congrArg (· ≫ e) hf)) ≫
        ((F.mapComp f e).hom ≫ θ.hom ▷ F.map e ≫ f' ◁ θe.hom) ≫
          eqToHom (congrArg₂ (· ≫ ·) hf' he.symm) := by
  subst hθe hf hf' he
  obtain rfl : θ₀ = θ := Iso.ext (by simpa using H)
  simp

private theorem conj_map₂_eqToHom_of_eq {f f₀ g g₀ : a ⟶ b} {f' f₀' g' g₀' : F.obj a ⟶ F.obj b}
    (hf : f₀ = f) (hf' : f' = f₀') (hg : g₀ = g) (hg' : g' = g₀') (θf : F.map f ≅ f')
    (θf₀ : F.map f₀ ≅ f₀') (θg : F.map g ≅ g') (θg₀ : F.map g₀ ≅ g₀')
    (Hf : θf₀.hom = F.map₂ (eqToHom hf) ≫ θf.hom ≫ eqToHom hf')
    (Hg : θg₀.hom = F.map₂ (eqToHom hg) ≫ θg.hom ≫ eqToHom hg') {η : f ⟶ g} {η' : f' ⟶ g'}
    (Hη : F.map₂ η = θf.hom ≫ η' ≫ θg.inv) :
    θf₀.inv ≫ F.map₂ (eqToHom hf ≫ η ≫ eqToHom hg.symm) ≫ θg₀.hom =
      eqToHom hf'.symm ≫ η' ≫ eqToHom hg' := by
  subst hf hf' hg hg'
  obtain rfl : θf₀ = θf := Iso.ext (by simpa using Hf)
  obtain rfl : θg₀ = θg := Iso.ext (by simpa using Hg)
  simp [Hη]

private theorem conj_map₂_eqToHom_comp_comp {f f₀ g g₀ h k : a ⟶ b}
    {f' f₀' g' g₀' h' k' : F.obj a ⟶ F.obj b} (hf : f₀ = f) (hf' : f' = f₀') (hg : g₀ = g)
    (hg' : g' = g₀') (θf : F.map f ≅ f') (θf₀ : F.map f₀ ≅ f₀') (θg : F.map g ≅ g')
    (θg₀ : F.map g₀ ≅ g₀') (θh : F.map h ≅ h') (θk : F.map k ≅ k')
    (Hf : θf₀.hom = F.map₂ (eqToHom hf) ≫ θf.hom ≫ eqToHom hf')
    (Hg : θg₀.hom = F.map₂ (eqToHom hg) ≫ θg.hom ≫ eqToHom hg') {α : f ⟶ h} {β : k ⟶ g}
    {α' : f' ⟶ h'} {β' : k' ⟶ g'} (Hα : F.map₂ α = θf.hom ≫ α' ≫ θh.inv)
    (Hβ : F.map₂ β = θk.hom ≫ β' ≫ θg.inv) (γ : h ⟶ k) :
    θf₀.inv ≫ F.map₂ (eqToHom hf ≫ α ≫ γ ≫ β ≫ eqToHom hg.symm) ≫ θg₀.hom =
      eqToHom hf'.symm ≫ α' ≫ (θh.inv ≫ F.map₂ γ ≫ θk.hom) ≫ β' ≫ eqToHom hg' := by
  subst hf hf' hg hg'
  obtain rfl : θf₀ = θf := Iso.ext (by simpa using Hf)
  obtain rfl : θg₀ = θg := Iso.ext (by simpa using Hg)
  simp [Hα, Hβ]

end Comparison

inductive _root_.CategoryTheory.FreeBicategory.Hom.IsGeneratorOrId :
    ∀ {a b : FreeBicategory V}, (a ⟶ b) → Prop
  | of {a b : V} (e : a ⟶ b) : IsGeneratorOrId (Hom.of (B := V) e)
  | id (a : FreeBicategory V) : IsGeneratorOrId (Hom.id (B := V) a)

theorem _root_.CategoryTheory.FreeBicategory.Hom.isGeneratorOrId_homOfEq_id
    {a b : FreeBicategory V} (h : a = b) :
    Hom.IsGeneratorOrId (Quiver.homOfEq (Hom.id (B := V) a) rfl h) := by
  subst h
  exact .id a

variable (G : Prefunctor V B)

theorem liftMapIso_inclusionPathAux (F : B ⥤ᵖ C) {x : V} : ∀ {y : V} (p : Path x y),
    liftMapIso G F (inclusionPathAux p) = pathCompMapIso G F p
  | _, .nil => rfl
  | _, .cons p e =>
    mapComp_trans_whiskerRightIso_trans_refl F (G.map e) (liftMapIso_inclusionPathAux F p)

variable (F : StrictlyUnitaryPseudofunctor B C)

theorem map_lift_map_of_isGeneratorOrId {a b : FreeBicategory V} {f : a ⟶ b}
    (hf : Hom.IsGeneratorOrId f) :
    F.map ((lift G).map f) = (lift (G ⋙q F.toPrefunctor)).map f := by
  cases hf with
  | of e => rfl
  | id => exact F.map_id _

theorem liftMapIso_of_isGeneratorOrId {a b : FreeBicategory V} {f : a ⟶ b}
    (hf : Hom.IsGeneratorOrId f) :
    liftMapIso G F.toPseudofunctor f = eqToIso (map_lift_map_of_isGeneratorOrId G F hf) := by
  cases hf with
  | of e => rfl
  | id => exact F.mapId_eq_eqToIso _

variable {W : Type u₃} [Quiver.{v₃} W] (H : Prefunctor W (FreeBicategory V))
  (hH : ∀ {v w : W} (e : v ⟶ w), Hom.IsGeneratorOrId (H.map e))

include hH in
theorem pathComp_comp_lift_comp {x : W} : ∀ {y : W} (p : Path x y),
    pathComp ((H ⋙q (lift G).toPrefunctor) ⋙q F.toPrefunctor) p =
      (lift (G ⋙q F.toPrefunctor)).map (pathComp H p)
  | _, .nil => rfl
  | _, .cons p e => congrArg₂ (· ≫ ·) (pathComp_comp_lift_comp p)
    (map_lift_map_of_isGeneratorOrId G F (hH e))

theorem pathCompMapIso_comp_lift {x : W} : ∀ {y : W} (p : Path x y),
    (pathCompMapIso (H ⋙q (lift G).toPrefunctor) F.toPseudofunctor p).hom =
      F.map₂ (eqToHom (pathComp_comp_lift H G p)) ≫
        (liftMapIso G F.toPseudofunctor (pathComp H p)).hom ≫
          eqToHom (pathComp_comp_lift_comp G F H hH p).symm
  | _, .nil => ((congrArg₂ (· ≫ ·) (F.map₂_id _) (Category.comp_id _)).trans
    (Category.id_comp _)).symm
  | _, .cons p e => mapComp_hom_whiskerRight_eqToHom_eqToIso F.toPseudofunctor
    ((lift G).map (H.map e)) (pathComp_comp_lift H G p)
    (pathComp_comp_lift_comp G F H hH p).symm (liftMapIso G F.toPseudofunctor (H.map e))
    (map_lift_map_of_isGeneratorOrId G F (hH e)) (liftMapIso_of_isGeneratorOrId G F (hH e))
    (liftMapIso G F.toPseudofunctor (pathComp H p))
    (pathCompMapIso (H ⋙q (lift G).toPrefunctor) F.toPseudofunctor p)
    (pathCompMapIso_comp_lift p)

theorem pathCompMap₂_comp_lift_map₂ {x y : W} {p q : Path x y}
    (θ : pathComp H p ⟶ pathComp H q) :
    pathCompMap₂ (H ⋙q (lift G).toPrefunctor) F.toPseudofunctor
        (eqToHom (pathComp_comp_lift H G p) ≫ (lift G).map₂ θ ≫
          eqToHom (pathComp_comp_lift H G q).symm) =
      eqToHom (pathComp_comp_lift_comp G F H hH p) ≫
        (lift (G ⋙q F.toPrefunctor)).map₂ θ ≫
          eqToHom (pathComp_comp_lift_comp G F H hH q).symm :=
  conj_map₂_eqToHom_of_eq F.toPseudofunctor (pathComp_comp_lift H G p)
    (pathComp_comp_lift_comp G F H hH p).symm (pathComp_comp_lift H G q)
    (pathComp_comp_lift_comp G F H hH q).symm (liftMapIso G F.toPseudofunctor (pathComp H p))
    (pathCompMapIso (H ⋙q (lift G).toPrefunctor) F.toPseudofunctor p)
    (liftMapIso G F.toPseudofunctor (pathComp H q))
    (pathCompMapIso (H ⋙q (lift G).toPrefunctor) F.toPseudofunctor q)
    (pathCompMapIso_comp_lift G F H hH p) (pathCompMapIso_comp_lift G F H hH q)
    (map₂_lift_map₂ G F.toPseudofunctor θ)

theorem pathCompMap₂_comp_lift_map₂_comp_comp {x y : W} {p q : Path x y}
    {p' q' : Path (V := V) (H.obj x) (H.obj y)}
    (θ₁ : pathComp H p ⟶ (inclusionPathAux p' : H.obj x ⟶ H.obj y))
    (γ : pathComp G p' ⟶ pathComp G q')
    (θ₂ : @Quiver.Hom (H.obj x ⟶ H.obj y) _ (inclusionPathAux q') (pathComp H q)) :
    pathCompMap₂ (H ⋙q (lift G).toPrefunctor) F.toPseudofunctor
        (eqToHom (pathComp_comp_lift H G p) ≫ (lift G).map₂ θ₁ ≫ γ ≫ (lift G).map₂ θ₂ ≫
          eqToHom (pathComp_comp_lift H G q).symm) =
      eqToHom (pathComp_comp_lift_comp G F H hH p) ≫
        (lift (G ⋙q F.toPrefunctor)).map₂ θ₁ ≫ pathCompMap₂ G F.toPseudofunctor γ ≫
          (lift (G ⋙q F.toPrefunctor)).map₂ θ₂ ≫
            eqToHom (pathComp_comp_lift_comp G F H hH q).symm :=
  conj_map₂_eqToHom_comp_comp F.toPseudofunctor (pathComp_comp_lift H G p)
    (pathComp_comp_lift_comp G F H hH p).symm (pathComp_comp_lift H G q)
    (pathComp_comp_lift_comp G F H hH q).symm (liftMapIso G F.toPseudofunctor (pathComp H p))
    (pathCompMapIso (H ⋙q (lift G).toPrefunctor) F.toPseudofunctor p)
    (liftMapIso G F.toPseudofunctor (pathComp H q))
    (pathCompMapIso (H ⋙q (lift G).toPrefunctor) F.toPseudofunctor q)
    (pathCompMapIso G F.toPseudofunctor p') (pathCompMapIso G F.toPseudofunctor q')
    (pathCompMapIso_comp_lift G F H hH p) (pathCompMapIso_comp_lift G F H hH q)
    (liftMapIso_inclusionPathAux G F.toPseudofunctor p' ▸ map₂_lift_map₂ G F.toPseudofunctor θ₁)
    (liftMapIso_inclusionPathAux G F.toPseudofunctor q' ▸ map₂_lift_map₂ G F.toPseudofunctor θ₂)
    γ

end StrictlyUnitary

end CategoryTheory.Bicategory
